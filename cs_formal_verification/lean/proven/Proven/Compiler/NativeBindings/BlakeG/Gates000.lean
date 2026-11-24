module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.BlakeG
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeGCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.BlakeG
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- The actual native sparse relation supplies gate 0. -/
theorem gate0 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeG.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate0.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate0.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨0, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate0 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[20]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[20]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨20, by decide⟩))

/-- The actual native sparse relation supplies gate 1. -/
theorem gate1 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeG.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate1.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate1.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨1, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate1 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[21]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[21]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨21, by decide⟩))

/-- The actual native sparse relation supplies gate 2. -/
theorem gate2 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeG.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate2.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate2.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨2, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate2 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[22]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[22]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨22, by decide⟩))

/-- The actual native sparse relation supplies gate 3. -/
theorem gate3 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeG.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate3.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate3.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨3, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate3 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[23]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[23]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨23, by decide⟩))

/-- The actual native sparse relation supplies gate 4. -/
theorem gate4 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeG.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate4.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate4.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨4, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate4 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[24]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[24]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨24, by decide⟩))

/-- The actual native sparse relation supplies gate 5. -/
theorem gate5 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeG.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate5.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate5.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨5, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate5 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[25]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[25]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨25, by decide⟩))

/-- The actual native sparse relation supplies gate 6. -/
theorem gate6 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeG.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate6.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate6.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨6, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate6 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[26]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[26]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨26, by decide⟩))

/-- The actual native sparse relation supplies gate 7. -/
theorem gate7 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeG.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate7.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate7.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨7, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate7 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[27]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[27]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨27, by decide⟩))

/-- The actual native sparse relation supplies gate 8. -/
theorem gate8 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeG.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate8.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate8.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨8, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate8 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[28]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[28]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨28, by decide⟩))

/-- The actual native sparse relation supplies gate 9. -/
theorem gate9 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeG.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate9.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate9.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨9, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate9 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[29]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[29]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨29, by decide⟩))

/-- The actual native sparse relation supplies gate 10. -/
theorem gate10 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeG.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate10.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate10.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨10, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate10 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[30]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[30]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨30, by decide⟩))

/-- The actual native sparse relation supplies gate 11. -/
theorem gate11 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeG.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate11.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate11.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨11, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate11 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[31]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[31]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨31, by decide⟩))

/-- The actual native sparse relation supplies gate 12. -/
theorem gate12 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeG.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate12.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate12.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨12, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate12 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[32]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[32]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨32, by decide⟩))

/-- The actual native sparse relation supplies gate 13. -/
theorem gate13 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeG.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate13.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate13.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨13, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate13 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[33]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[33]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨33, by decide⟩))

/-- The actual native sparse relation supplies gate 14. -/
theorem gate14 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeG.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate14.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate14.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨14, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate14 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[34]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[34]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨34, by decide⟩))

/-- The actual native sparse relation supplies gate 15. -/
theorem gate15 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeG.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate15.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate15.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gatesChecked _ (List.get_mem _ ⟨15, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate15 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[35]'(by decide)).1 (((Airbender.Compiler.Captures.BlakeG.imported.circuit).layers[0]'(by decide)).cached_relations[35]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨35, by decide⟩))

/-- This batch retains every native scalar equation at these positions. -/
theorem gates000 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeG.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate0, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate1, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate2, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate3, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate4, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate5, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate6, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate7, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate8, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate9, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate10, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate11, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate12, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate13, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate14, Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate15], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0 :=
  (cons_holds (gate0 physical accepted) (cons_holds (gate1 physical accepted) (cons_holds (gate2 physical accepted) (cons_holds (gate3 physical accepted) (cons_holds (gate4 physical accepted) (cons_holds (gate5 physical accepted) (cons_holds (gate6 physical accepted) (cons_holds (gate7 physical accepted) (cons_holds (gate8 physical accepted) (cons_holds (gate9 physical accepted) (cons_holds (gate10 physical accepted) (cons_holds (gate11 physical accepted) (cons_holds (gate12 physical accepted) (cons_holds (gate13 physical accepted) (cons_holds (gate14 physical accepted) (cons_holds (gate15 physical accepted) (by intro gate member; cases member)))))))))))))))))
end Airbender.Compiler.NativeBindings.BlakeG
