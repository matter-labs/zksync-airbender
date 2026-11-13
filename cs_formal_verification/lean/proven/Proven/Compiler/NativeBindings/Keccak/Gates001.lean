module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.Keccak
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.Keccak
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- The actual native sparse relation supplies gate 16. -/
theorem gate16 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate16.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate16.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨16, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate16 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[46]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[46]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨46, by decide⟩))

/-- The actual native sparse relation supplies gate 17. -/
theorem gate17 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate17.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate17.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨17, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate17 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[47]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[47]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨47, by decide⟩))

/-- The actual native sparse relation supplies gate 18. -/
theorem gate18 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate18.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate18.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨18, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate18 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[48]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[48]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨48, by decide⟩))

/-- The actual native sparse relation supplies gate 19. -/
theorem gate19 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate19.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate19.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨19, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate19 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[49]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[49]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨49, by decide⟩))

/-- The actual native sparse relation supplies gate 20. -/
theorem gate20 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate20.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate20.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨20, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate20 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[50]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[50]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨50, by decide⟩))

/-- The actual native sparse relation supplies gate 21. -/
theorem gate21 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate21.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate21.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨21, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate21 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[51]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[51]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨51, by decide⟩))

/-- The actual native sparse relation supplies gate 22. -/
theorem gate22 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate22.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate22.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨22, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate22 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[52]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[52]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨52, by decide⟩))

/-- The actual native sparse relation supplies gate 23. -/
theorem gate23 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate23.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate23.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨23, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate23 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[53]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[53]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨53, by decide⟩))

/-- The actual native sparse relation supplies gate 24. -/
theorem gate24 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate24.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate24.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨24, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate24 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[54]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[54]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨54, by decide⟩))

/-- The actual native sparse relation supplies gate 25. -/
theorem gate25 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate25.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate25.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨25, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate25 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[55]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[55]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨55, by decide⟩))

/-- The actual native sparse relation supplies gate 26. -/
theorem gate26 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate26.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate26.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨26, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate26 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[56]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[56]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨56, by decide⟩))

/-- The actual native sparse relation supplies gate 27. -/
theorem gate27 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate27.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate27.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨27, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate27 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[57]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[57]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨57, by decide⟩))

/-- The actual native sparse relation supplies gate 28. -/
theorem gate28 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate28.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate28.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨28, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate28 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[58]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[58]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨58, by decide⟩))

/-- The actual native sparse relation supplies gate 29. -/
theorem gate29 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate29.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate29.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨29, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate29 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.cache (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[59]'(by decide)).1 (((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).cached_relations[59]'(by decide)).2).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (cache_at accepted ⟨0, by decide⟩ ⟨59, by decide⟩))

/-- The actual native sparse relation supplies gate 30. -/
theorem gate30 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate30.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate30.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨30, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate30 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨0, by decide⟩))

/-- The actual native sparse relation supplies gate 31. -/
theorem gate31 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate31.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate31.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨31, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate31 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[32]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨32, by decide⟩))

/-- This batch retains every native scalar equation at these positions. -/
theorem gates001 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate16, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate17, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate18, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate19, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate20, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate21, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate22, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate23, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate24, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate25, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate26, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate27, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate28, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate29, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate30, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate31], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 :=
  (cons_holds (gate16 physical accepted) (cons_holds (gate17 physical accepted) (cons_holds (gate18 physical accepted) (cons_holds (gate19 physical accepted) (cons_holds (gate20 physical accepted) (cons_holds (gate21 physical accepted) (cons_holds (gate22 physical accepted) (cons_holds (gate23 physical accepted) (cons_holds (gate24 physical accepted) (cons_holds (gate25 physical accepted) (cons_holds (gate26 physical accepted) (cons_holds (gate27 physical accepted) (cons_holds (gate28 physical accepted) (cons_holds (gate29 physical accepted) (cons_holds (gate30 physical accepted) (cons_holds (gate31 physical accepted) (by intro gate member; cases member)))))))))))))))))
end Airbender.Compiler.NativeBindings.Keccak
