module
public import Proven.Compiler.Reverse
public import Proven.Compiler.NativeBindings.BlakeRound
public import Proven.KernelExact

@[expose] public section
namespace Airbender.Compiler.NativeExtension.BlakeRound
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option warningAsError true
set_option maxRecDepth 65536

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse48 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[136]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[136]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate48.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨48, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate48 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[136]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[136]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨48, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse49 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[137]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[137]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate49.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨49, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate49 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[137]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[137]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨49, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse50 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[138]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[138]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate50.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨50, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate50 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[138]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[138]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨50, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse51 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[139]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[139]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate51.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨51, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate51 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[139]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[139]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨51, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse52 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[140]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[140]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate52.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨52, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate52 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[140]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[140]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨52, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse53 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[141]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[141]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate53.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨53, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate53 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[141]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[141]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨53, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse54 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[142]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[142]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate54.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨54, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate54 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[142]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[142]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨54, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse55 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[143]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[143]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate55.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨55, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate55 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[143]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[143]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨55, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse56 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[144]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[144]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate56.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨56, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate56 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[144]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[144]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨56, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse57 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[145]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[145]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate57.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨57, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate57 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[145]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[145]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨57, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse58 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[146]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[146]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate58.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨58, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate58 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[146]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[146]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨58, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse59 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[147]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[147]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate59.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨59, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate59 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[147]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[147]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨59, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse60 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[148]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[148]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate60.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨60, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate60 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[148]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[148]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨60, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse61 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[149]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[149]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate61.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨61, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate61 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[149]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[149]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨61, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse62 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[150]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[150]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate62.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨62, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate62 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[150]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[150]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨62, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse63 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[151]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[151]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate63.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gatesChecked _ (List.get_mem _ ⟨63, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate63 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[151]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[151]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨63, by decide⟩)))

theorem batch003 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    ∀ clause ∈ [(Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[136]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[136]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[137]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[137]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[138]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[138]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[139]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[139]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[140]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[140]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[141]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[141]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[142]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[142]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[143]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[143]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[144]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[144]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[145]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[145]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[146]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[146]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[147]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[147]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[148]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[148]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[149]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[149]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[150]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[150]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[151]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[151]'(by decide)).2)], clause.residual physical = 0 :=
  (cons_zero (reverse48 physical holds) (cons_zero (reverse49 physical holds) (cons_zero (reverse50 physical holds) (cons_zero (reverse51 physical holds) (cons_zero (reverse52 physical holds) (cons_zero (reverse53 physical holds) (cons_zero (reverse54 physical holds) (cons_zero (reverse55 physical holds) (cons_zero (reverse56 physical holds) (cons_zero (reverse57 physical holds) (cons_zero (reverse58 physical holds) (cons_zero (reverse59 physical holds) (cons_zero (reverse60 physical holds) (cons_zero (reverse61 physical holds) (cons_zero (reverse62 physical holds) (cons_zero (reverse63 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member)))))))))))))))))
end Airbender.Compiler.NativeExtension.BlakeRound
