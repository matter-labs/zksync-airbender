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

/-- The actual native sparse relation supplies gate 8. -/
theorem gate8 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate8.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate8.check = true :=
    all_at (index := 8) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate8) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[96]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry96 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate8 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry96).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry96).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate8, Expression.value, Function.comp_apply, coordinate2, coordinate635, coordinate684, coordinate777]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨96, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry96 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 9. -/
theorem gate9 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate9.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate9.check = true :=
    all_at (index := 9) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate9) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[97]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry97 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate9 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry97).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry97).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate9, Expression.value, Function.comp_apply, coordinate1, coordinate636, coordinate685, coordinate778]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨97, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry97 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 10. -/
theorem gate10 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate10.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate10.check = true :=
    all_at (index := 10) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate10) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[98]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry98 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate10 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry98).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry98).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate10, Expression.value, Function.comp_apply, coordinate2, coordinate636, coordinate686, coordinate779]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨98, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry98 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 11. -/
theorem gate11 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate11.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate11.check = true :=
    all_at (index := 11) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate11) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[99]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry99 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate11 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry99).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry99).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate11, Expression.value, Function.comp_apply, coordinate1, coordinate637, coordinate687, coordinate780]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨99, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry99 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 12. -/
theorem gate12 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate12.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate12.check = true :=
    all_at (index := 12) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate12) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[100]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry100 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate12 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry100).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry100).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate12, Expression.value, Function.comp_apply, coordinate2, coordinate637, coordinate688, coordinate781]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨100, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry100 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 13. -/
theorem gate13 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate13.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate13.check = true :=
    all_at (index := 13) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate13) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[101]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry101 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate13 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry101).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry101).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate13, Expression.value, Function.comp_apply, coordinate1, coordinate638, coordinate689, coordinate782]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨101, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry101 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 14. -/
theorem gate14 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate14.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate14.check = true :=
    all_at (index := 14) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate14) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[102]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry102 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate14 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry102).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry102).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate14, Expression.value, Function.comp_apply, coordinate2, coordinate638, coordinate690, coordinate783]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨102, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry102 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 15. -/
theorem gate15 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate15.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate15.check = true :=
    all_at (index := 15) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate15) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[103]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry103 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate15 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry103).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry103).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate15, Expression.value, Function.comp_apply, coordinate1, coordinate639, coordinate691, coordinate784]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨103, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry103 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- This batch retains every native scalar equation at these positions. -/
theorem gates001 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate8, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate9, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate10, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate11, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate12, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate13, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate14, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate15], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate8 physical accepted) (cons_holds (gate9 physical accepted) (cons_holds (gate10 physical accepted) (cons_holds (gate11 physical accepted) (cons_holds (gate12 physical accepted) (cons_holds (gate13 physical accepted) (cons_holds (gate14 physical accepted) (cons_holds (gate15 physical accepted) (by intro gate member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
