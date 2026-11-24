module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.WordMemory
public import Proven.GKRProtocol.CleanArithmeticNative.WordMemoryCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.WordMemory
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- The actual native sparse relation supplies gate 0. -/
theorem gate0 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate0.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate0.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨0, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate0 (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).cached_relations[8]'(by decide)).1 (((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).cached_relations[8]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨8, by decide⟩))

/-- The actual native sparse relation supplies gate 1. -/
theorem gate1 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate1.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate1.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨1, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate1 (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).cached_relations[9]'(by decide)).1 (((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).cached_relations[9]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨9, by decide⟩))

/-- The actual native sparse relation supplies gate 2. -/
theorem gate2 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate2.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate2.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨2, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate2 (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).cached_relations[10]'(by decide)).1 (((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).cached_relations[10]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨10, by decide⟩))

/-- The actual native sparse relation supplies gate 3. -/
theorem gate3 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate3.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate3.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨3, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate3 (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).cached_relations[11]'(by decide)).1 (((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).cached_relations[11]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨11, by decide⟩))

/-- The actual native sparse relation supplies gate 4. -/
theorem gate4 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate4.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate4.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨4, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate4 (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).cached_relations[12]'(by decide)).1 (((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).cached_relations[12]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨12, by decide⟩))

/-- The actual native sparse relation supplies gate 5. -/
theorem gate5 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate5.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate5.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨5, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate5 (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).cached_relations[13]'(by decide)).1 (((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).cached_relations[13]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨13, by decide⟩))

/-- The actual native sparse relation supplies gate 6. -/
theorem gate6 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate6.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate6.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨6, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate6 (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨0, by decide⟩))

/-- The actual native sparse relation supplies gate 7. -/
theorem gate7 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate7.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate7.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨7, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate7 (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[5]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨5, by decide⟩))

/-- The actual native sparse relation supplies gate 8. -/
theorem gate8 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate8.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate8.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨8, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate8 (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[6]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨6, by decide⟩))

/-- The actual native sparse relation supplies gate 9. -/
theorem gate9 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate9.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate9.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨9, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate9 (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[7]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨7, by decide⟩))

/-- The actual native sparse relation supplies gate 10. -/
theorem gate10 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate10.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate10.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨10, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate10 (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[8]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨8, by decide⟩))

/-- The actual native sparse relation supplies gate 11. -/
theorem gate11 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate11.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate11.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨11, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate11 (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[9]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨9, by decide⟩))

/-- The actual native sparse relation supplies gate 12. -/
theorem gate12 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate12.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate12.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨12, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate12 (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[10]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨10, by decide⟩))

/-- The actual native sparse relation supplies gate 13. -/
theorem gate13 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate13.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate13.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨13, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate13 (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[11]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨11, by decide⟩))

/-- The actual native sparse relation supplies gate 14. -/
theorem gate14 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate14.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate14.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨14, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate14 (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[12]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨12, by decide⟩))

/-- The actual native sparse relation supplies gate 15. -/
theorem gate15 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate15.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate15.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨15, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate15 (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[14]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨14, by decide⟩))

/-- This batch retains every native scalar equation at these positions. -/
theorem gates000 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate0, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate1, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate2, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate3, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate4, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate5, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate6, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate7, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate8, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate9, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate10, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate11, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate12, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate13, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate14, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate15], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 :=
  (cons_holds (gate0 physical accepted) (cons_holds (gate1 physical accepted) (cons_holds (gate2 physical accepted) (cons_holds (gate3 physical accepted) (cons_holds (gate4 physical accepted) (cons_holds (gate5 physical accepted) (cons_holds (gate6 physical accepted) (cons_holds (gate7 physical accepted) (cons_holds (gate8 physical accepted) (cons_holds (gate9 physical accepted) (cons_holds (gate10 physical accepted) (cons_holds (gate11 physical accepted) (cons_holds (gate12 physical accepted) (cons_holds (gate13 physical accepted) (cons_holds (gate14 physical accepted) (cons_holds (gate15 physical accepted) (by intro gate member; cases member)))))))))))))))))
end Airbender.Compiler.NativeBindings.WordMemory
