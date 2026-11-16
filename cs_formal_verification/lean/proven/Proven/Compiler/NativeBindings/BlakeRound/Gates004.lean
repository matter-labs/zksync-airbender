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

/-- The actual native sparse relation supplies gate 72. -/
theorem gate72 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate72.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate72.check = true :=
    all_at (index := 72) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate72) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[160]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry160 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate72 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry160).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry160).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate72, Expression.value, Function.comp_apply, coordinate2, coordinate667, coordinate748, coordinate841]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨160, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry160 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 73. -/
theorem gate73 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate73.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate73.check = true :=
    all_at (index := 73) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate73) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[161]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry161 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate73 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry161).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry161).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate73, Expression.value, Function.comp_apply, coordinate1, coordinate668, coordinate749, coordinate842]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨161, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry161 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 74. -/
theorem gate74 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate74.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate74.check = true :=
    all_at (index := 74) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate74) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[162]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry162 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate74 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry162).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry162).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate74, Expression.value, Function.comp_apply, coordinate2, coordinate668, coordinate750, coordinate843]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨162, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry162 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 75. -/
theorem gate75 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate75.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate75.check = true :=
    all_at (index := 75) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate75) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[163]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry163 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate75 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry163).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry163).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate75, Expression.value, Function.comp_apply, coordinate1, coordinate669, coordinate751, coordinate844]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨163, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry163 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 76. -/
theorem gate76 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate76.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate76.check = true :=
    all_at (index := 76) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate76) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[164]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry164 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate76 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry164).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry164).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate76, Expression.value, Function.comp_apply, coordinate2, coordinate669, coordinate752, coordinate845]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨164, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry164 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 77. -/
theorem gate77 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate77.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate77.check = true :=
    all_at (index := 77) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate77) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[165]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry165 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate77 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry165).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry165).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate77, Expression.value, Function.comp_apply, coordinate1, coordinate670, coordinate753, coordinate846]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨165, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry165 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 78. -/
theorem gate78 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate78.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate78.check = true :=
    all_at (index := 78) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate78) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[166]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry166 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate78 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry166).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry166).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate78, Expression.value, Function.comp_apply, coordinate2, coordinate670, coordinate754, coordinate847]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨166, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry166 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 79. -/
theorem gate79 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate79.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate79.check = true :=
    all_at (index := 79) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate79) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[167]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry167 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate79 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry167).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry167).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate79, Expression.value, Function.comp_apply, coordinate1, coordinate671, coordinate755, coordinate848]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨167, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry167 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- This batch retains every native scalar equation at these positions. -/
theorem gates004 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate64, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate65, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate66, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate67, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate68, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate69, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate70, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate71, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate72, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate73, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate74, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate75, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate76, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate77, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate78, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate79], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate64 physical accepted) (cons_holds (gate65 physical accepted) (cons_holds (gate66 physical accepted) (cons_holds (gate67 physical accepted) (cons_holds (gate68 physical accepted) (cons_holds (gate69 physical accepted) (cons_holds (gate70 physical accepted) (cons_holds (gate71 physical accepted) (cons_holds (gate72 physical accepted) (cons_holds (gate73 physical accepted) (cons_holds (gate74 physical accepted) (cons_holds (gate75 physical accepted) (cons_holds (gate76 physical accepted) (cons_holds (gate77 physical accepted) (cons_holds (gate78 physical accepted) (cons_holds (gate79 physical accepted) (by intro gate member; cases member)))))))))))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
