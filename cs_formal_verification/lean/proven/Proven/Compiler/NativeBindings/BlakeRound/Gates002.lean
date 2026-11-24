module
public import Proven.Compiler.NativeLiteralBridge
public import Proven.Compiler.NativeBindings.BlakeRound.NativeData
public import Proven.Compiler.NativeBindings.BlakeRound.BankCoordinates
public import Proven.Compiler.NativeBindings.BlakeRound.CaptureData
public import Proven.KernelRfl
public import Human.Compiler.Captures.BlakeRound
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.BlakeRound
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- The actual native sparse relation supplies gate 16. -/
theorem gate16 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate16.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate16.check = true :=
    all_at (index := 16) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate16) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[104]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry104 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate16 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry104).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry104).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate16, Expression.value, Function.comp_apply, coordinate2, coordinate639, coordinate692, coordinate785]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨104, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry104 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 17. -/
theorem gate17 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate17.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate17.check = true :=
    all_at (index := 17) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate17) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[105]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry105 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate17 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry105).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry105).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate17, Expression.value, Function.comp_apply, coordinate1, coordinate640, coordinate693, coordinate786]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨105, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry105 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 18. -/
theorem gate18 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate18.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate18.check = true :=
    all_at (index := 18) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate18) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[106]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry106 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate18 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry106).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry106).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate18, Expression.value, Function.comp_apply, coordinate2, coordinate640, coordinate694, coordinate787]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨106, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry106 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 19. -/
theorem gate19 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate19.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate19.check = true :=
    all_at (index := 19) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate19) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[107]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry107 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate19 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry107).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry107).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate19, Expression.value, Function.comp_apply, coordinate1, coordinate641, coordinate695, coordinate788]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨107, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry107 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 20. -/
theorem gate20 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate20.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate20.check = true :=
    all_at (index := 20) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate20) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[108]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry108 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate20 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry108).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry108).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate20, Expression.value, Function.comp_apply, coordinate2, coordinate641, coordinate696, coordinate789]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨108, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry108 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 21. -/
theorem gate21 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate21.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate21.check = true :=
    all_at (index := 21) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate21) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[109]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry109 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate21 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry109).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry109).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate21, Expression.value, Function.comp_apply, coordinate1, coordinate642, coordinate697, coordinate790]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨109, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry109 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 22. -/
theorem gate22 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate22.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate22.check = true :=
    all_at (index := 22) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate22) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[110]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry110 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate22 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry110).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry110).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate22, Expression.value, Function.comp_apply, coordinate2, coordinate642, coordinate698, coordinate791]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨110, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry110 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 23. -/
theorem gate23 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate23.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate23.check = true :=
    all_at (index := 23) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate23) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[111]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry111 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate23 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry111).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry111).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate23, Expression.value, Function.comp_apply, coordinate1, coordinate643, coordinate699, coordinate792]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨111, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry111 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- This batch retains every native scalar equation at these positions. -/
theorem gates002 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate16, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate17, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate18, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate19, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate20, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate21, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate22, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate23], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate16 physical accepted) (cons_holds (gate17 physical accepted) (cons_holds (gate18 physical accepted) (cons_holds (gate19 physical accepted) (cons_holds (gate20 physical accepted) (cons_holds (gate21 physical accepted) (cons_holds (gate22 physical accepted) (cons_holds (gate23 physical accepted) (by intro gate member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
