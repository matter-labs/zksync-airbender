module
public import Proven.Compiler.Reverse
public import Proven.Compiler.NativeBindings.BlakeG
public import Proven.KernelExact

@[expose] public section
namespace Airbender.Compiler.NativeExtension.BlakeG
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option warningAsError true
set_option maxRecDepth 65536

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse0 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[20]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[20]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate0.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨0, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate0 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[20]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[20]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨0, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse1 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[21]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[21]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate1.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨1, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate1 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[21]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[21]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨1, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse2 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[22]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[22]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate2.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨2, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate2 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[22]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[22]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨2, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse3 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[23]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[23]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate3.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨3, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate3 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[23]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[23]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨3, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse4 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[24]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[24]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate4.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨4, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate4 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[24]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[24]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨4, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse5 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[25]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[25]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate5.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨5, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate5 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[25]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[25]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨5, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse6 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[26]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[26]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate6.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨6, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate6 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[26]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[26]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨6, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse7 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[27]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[27]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate7.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨7, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate7 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[27]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[27]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨7, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse8 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[28]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[28]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate8.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨8, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate8 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[28]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[28]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨8, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse9 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[29]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[29]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate9.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨9, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate9 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[29]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[29]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨9, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse10 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[30]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[30]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate10.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨10, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate10 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[30]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[30]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨10, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse11 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[31]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[31]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate11.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨11, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate11 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[31]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[31]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨11, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse12 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[32]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[32]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate12.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨12, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate12 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[32]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[32]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨12, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse13 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[33]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[33]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate13.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨13, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate13 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[33]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[33]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨13, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse14 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[34]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[34]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate14.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨14, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate14 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[34]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[34]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨14, by decide⟩)))

/-- The complete arithmetic extension satisfies this actual native sparse relation. -/
theorem reverse15 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[35]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[35]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate15.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨15, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate15 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[35]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[35]'(by decide)).2).residual physical := by kernel_rfl
  exact binding.symm.trans ((sparse_checked checked _).trans
    (holds _ (List.get_mem _ ⟨15, by decide⟩)))

theorem batch000 (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0) :
    ∀ clause ∈ [(Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[20]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[20]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[21]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[21]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[22]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[22]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[23]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[23]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[24]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[24]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[25]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[25]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[26]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[26]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[27]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[27]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[28]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[28]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[29]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[29]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[30]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[30]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[31]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[31]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[32]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[32]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[33]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[33]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[34]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[34]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[35]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[35]'(by decide)).2)], clause.residual physical = 0 :=
  (cons_zero (reverse0 physical holds) (cons_zero (reverse1 physical holds) (cons_zero (reverse2 physical holds) (cons_zero (reverse3 physical holds) (cons_zero (reverse4 physical holds) (cons_zero (reverse5 physical holds) (cons_zero (reverse6 physical holds) (cons_zero (reverse7 physical holds) (cons_zero (reverse8 physical holds) (cons_zero (reverse9 physical holds) (cons_zero (reverse10 physical holds) (cons_zero (reverse11 physical holds) (cons_zero (reverse12 physical holds) (cons_zero (reverse13 physical holds) (cons_zero (reverse14 physical holds) (cons_zero (reverse15 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member)))))))))))))))))
end Airbender.Compiler.NativeExtension.BlakeG
