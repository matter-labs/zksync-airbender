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

/-- The actual native sparse relation supplies gate 56. -/
theorem gate56 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate56.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate56.check = true :=
    all_at (index := 56) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate56) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[144]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry144 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate56 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry144).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry144).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate56, Expression.value, Function.comp_apply, coordinate2, coordinate659, coordinate732, coordinate825]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨144, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry144 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 57. -/
theorem gate57 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate57.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate57.check = true :=
    all_at (index := 57) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate57) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[145]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry145 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate57 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry145).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry145).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate57, Expression.value, Function.comp_apply, coordinate1, coordinate660, coordinate733, coordinate826]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨145, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry145 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 58. -/
theorem gate58 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate58.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate58.check = true :=
    all_at (index := 58) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate58) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[146]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry146 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate58 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry146).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry146).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate58, Expression.value, Function.comp_apply, coordinate2, coordinate660, coordinate734, coordinate827]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨146, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry146 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 59. -/
theorem gate59 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate59.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate59.check = true :=
    all_at (index := 59) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate59) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[147]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry147 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate59 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry147).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry147).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate59, Expression.value, Function.comp_apply, coordinate1, coordinate661, coordinate735, coordinate828]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨147, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry147 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 60. -/
theorem gate60 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate60.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate60.check = true :=
    all_at (index := 60) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate60) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[148]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry148 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate60 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry148).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry148).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate60, Expression.value, Function.comp_apply, coordinate2, coordinate661, coordinate736, coordinate829]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨148, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry148 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 61. -/
theorem gate61 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate61.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate61.check = true :=
    all_at (index := 61) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate61) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[149]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry149 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate61 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry149).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry149).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate61, Expression.value, Function.comp_apply, coordinate1, coordinate662, coordinate737, coordinate830]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨149, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry149 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 62. -/
theorem gate62 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate62.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate62.check = true :=
    all_at (index := 62) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate62) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[150]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry150 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate62 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry150).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry150).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate62, Expression.value, Function.comp_apply, coordinate2, coordinate662, coordinate738, coordinate831]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨150, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry150 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 63. -/
theorem gate63 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate63.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate63.check = true :=
    all_at (index := 63) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate63) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[151]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry151 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate63 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry151).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry151).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate63, Expression.value, Function.comp_apply, coordinate1, coordinate663, coordinate739, coordinate832]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨151, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry151 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- This batch retains every native scalar equation at these positions. -/
theorem gates007 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate56, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate57, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate58, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate59, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate60, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate61, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate62, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate63], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate56 physical accepted) (cons_holds (gate57 physical accepted) (cons_holds (gate58 physical accepted) (cons_holds (gate59 physical accepted) (cons_holds (gate60 physical accepted) (cons_holds (gate61 physical accepted) (cons_holds (gate62 physical accepted) (cons_holds (gate63 physical accepted) (by intro gate member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
