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

/-- The actual native sparse relation supplies gate 64. -/
theorem gate64 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate64.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate64.check = true :=
    all_at (index := 64) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate64) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[152]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry152 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate64 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry152).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry152).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate64, Expression.value, Function.comp_apply, coordinate2, coordinate663, coordinate740, coordinate833]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨152, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry152 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 65. -/
theorem gate65 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate65.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate65.check = true :=
    all_at (index := 65) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate65) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[153]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry153 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate65 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry153).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry153).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate65, Expression.value, Function.comp_apply, coordinate1, coordinate664, coordinate741, coordinate834]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨153, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry153 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 66. -/
theorem gate66 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate66.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate66.check = true :=
    all_at (index := 66) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate66) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[154]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry154 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate66 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry154).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry154).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate66, Expression.value, Function.comp_apply, coordinate2, coordinate664, coordinate742, coordinate835]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨154, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry154 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 67. -/
theorem gate67 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate67.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate67.check = true :=
    all_at (index := 67) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate67) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[155]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry155 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate67 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry155).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry155).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate67, Expression.value, Function.comp_apply, coordinate1, coordinate665, coordinate743, coordinate836]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨155, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry155 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 68. -/
theorem gate68 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate68.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate68.check = true :=
    all_at (index := 68) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate68) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[156]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry156 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate68 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry156).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry156).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate68, Expression.value, Function.comp_apply, coordinate2, coordinate665, coordinate744, coordinate837]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨156, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry156 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 69. -/
theorem gate69 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate69.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate69.check = true :=
    all_at (index := 69) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate69) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[157]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry157 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate69 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry157).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry157).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate69, Expression.value, Function.comp_apply, coordinate1, coordinate666, coordinate745, coordinate838]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨157, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry157 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 70. -/
theorem gate70 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate70.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate70.check = true :=
    all_at (index := 70) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate70) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[158]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry158 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate70 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry158).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry158).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate70, Expression.value, Function.comp_apply, coordinate2, coordinate666, coordinate746, coordinate839]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨158, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry158 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 71. -/
theorem gate71 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate71.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate71.check = true :=
    all_at (index := 71) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate71) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[159]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry159 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate71 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry159).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry159).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate71, Expression.value, Function.comp_apply, coordinate1, coordinate667, coordinate747, coordinate840]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨159, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry159 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- This batch retains every native scalar equation at these positions. -/
theorem gates008 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate64, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate65, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate66, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate67, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate68, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate69, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate70, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate71], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate64 physical accepted) (cons_holds (gate65 physical accepted) (cons_holds (gate66 physical accepted) (cons_holds (gate67 physical accepted) (cons_holds (gate68 physical accepted) (cons_holds (gate69 physical accepted) (cons_holds (gate70 physical accepted) (cons_holds (gate71 physical accepted) (by intro gate member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
