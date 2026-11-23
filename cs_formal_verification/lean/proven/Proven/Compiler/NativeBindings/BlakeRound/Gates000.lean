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

/-- The actual native sparse relation supplies gate 0. -/
theorem gate0 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate0.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate0.check = true :=
    all_at (index := 0) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate0) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[88]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry88 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate0 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry88).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry88).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate0, Expression.value, Function.comp_apply, coordinate0, coordinate1, coordinate769]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨88, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry88 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 1. -/
theorem gate1 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate1.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate1.check = true :=
    all_at (index := 1) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate1) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[89]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry89 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate1 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry89).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry89).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate1, Expression.value, Function.comp_apply, coordinate1, coordinate632, coordinate677, coordinate770]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨89, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry89 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 2. -/
theorem gate2 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate2.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate2.check = true :=
    all_at (index := 2) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate2) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[90]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry90 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate2 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry90).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry90).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate2, Expression.value, Function.comp_apply, coordinate2, coordinate632, coordinate678, coordinate771]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨90, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry90 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 3. -/
theorem gate3 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate3.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate3.check = true :=
    all_at (index := 3) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate3) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[91]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry91 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate3 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry91).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry91).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate3, Expression.value, Function.comp_apply, coordinate1, coordinate633, coordinate679, coordinate772]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨91, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry91 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 4. -/
theorem gate4 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate4.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate4.check = true :=
    all_at (index := 4) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate4) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[92]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry92 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate4 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry92).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry92).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate4, Expression.value, Function.comp_apply, coordinate2, coordinate633, coordinate680, coordinate773]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨92, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry92 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 5. -/
theorem gate5 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate5.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate5.check = true :=
    all_at (index := 5) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate5) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[93]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry93 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate5 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry93).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry93).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate5, Expression.value, Function.comp_apply, coordinate1, coordinate634, coordinate681, coordinate774]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨93, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry93 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 6. -/
theorem gate6 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate6.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate6.check = true :=
    all_at (index := 6) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate6) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[94]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry94 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate6 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry94).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry94).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate6, Expression.value, Function.comp_apply, coordinate2, coordinate634, coordinate682, coordinate775]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨94, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry94 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 7. -/
theorem gate7 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate7.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate7.check = true :=
    all_at (index := 7) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate7) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[95]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry95 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate7 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry95).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry95).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate7, Expression.value, Function.comp_apply, coordinate1, coordinate635, coordinate683, coordinate776]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨95, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry95 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- This batch retains every native scalar equation at these positions. -/
theorem gates000 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate0, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate1, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate2, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate3, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate4, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate5, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate6, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate7], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate0 physical accepted) (cons_holds (gate1 physical accepted) (cons_holds (gate2 physical accepted) (cons_holds (gate3 physical accepted) (cons_holds (gate4 physical accepted) (cons_holds (gate5 physical accepted) (cons_holds (gate6 physical accepted) (cons_holds (gate7 physical accepted) (by intro gate member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
