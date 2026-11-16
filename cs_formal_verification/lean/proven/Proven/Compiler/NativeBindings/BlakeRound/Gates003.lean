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

/-- The actual native sparse relation supplies gate 48. -/
theorem gate48 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate48.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate48.check = true :=
    all_at (index := 48) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate48) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[136]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry136 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate48 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry136).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry136).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate48, Expression.value, Function.comp_apply, coordinate2, coordinate655, coordinate724, coordinate817]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨136, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry136 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 49. -/
theorem gate49 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate49.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate49.check = true :=
    all_at (index := 49) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate49) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[137]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry137 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate49 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry137).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry137).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate49, Expression.value, Function.comp_apply, coordinate1, coordinate656, coordinate725, coordinate818]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨137, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry137 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 50. -/
theorem gate50 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate50.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate50.check = true :=
    all_at (index := 50) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate50) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[138]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry138 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate50 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry138).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry138).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate50, Expression.value, Function.comp_apply, coordinate2, coordinate656, coordinate726, coordinate819]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨138, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry138 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 51. -/
theorem gate51 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate51.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate51.check = true :=
    all_at (index := 51) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate51) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[139]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry139 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate51 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry139).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry139).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate51, Expression.value, Function.comp_apply, coordinate1, coordinate657, coordinate727, coordinate820]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨139, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry139 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 52. -/
theorem gate52 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate52.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate52.check = true :=
    all_at (index := 52) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate52) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[140]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry140 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate52 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry140).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry140).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate52, Expression.value, Function.comp_apply, coordinate2, coordinate657, coordinate728, coordinate821]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨140, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry140 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 53. -/
theorem gate53 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate53.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate53.check = true :=
    all_at (index := 53) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate53) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[141]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry141 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate53 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry141).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry141).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate53, Expression.value, Function.comp_apply, coordinate1, coordinate658, coordinate729, coordinate822]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨141, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry141 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 54. -/
theorem gate54 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate54.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate54.check = true :=
    all_at (index := 54) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate54) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[142]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry142 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate54 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry142).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry142).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate54, Expression.value, Function.comp_apply, coordinate2, coordinate658, coordinate730, coordinate823]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨142, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry142 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 55. -/
theorem gate55 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate55.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate55.check = true :=
    all_at (index := 55) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate55) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[143]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry143 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate55 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry143).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry143).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate55, Expression.value, Function.comp_apply, coordinate1, coordinate659, coordinate731, coordinate824]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨143, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry143 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

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
theorem gates003 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate48, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate49, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate50, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate51, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate52, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate53, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate54, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate55, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate56, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate57, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate58, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate59, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate60, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate61, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate62, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate63], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate48 physical accepted) (cons_holds (gate49 physical accepted) (cons_holds (gate50 physical accepted) (cons_holds (gate51 physical accepted) (cons_holds (gate52 physical accepted) (cons_holds (gate53 physical accepted) (cons_holds (gate54 physical accepted) (cons_holds (gate55 physical accepted) (cons_holds (gate56 physical accepted) (cons_holds (gate57 physical accepted) (cons_holds (gate58 physical accepted) (cons_holds (gate59 physical accepted) (cons_holds (gate60 physical accepted) (cons_holds (gate61 physical accepted) (cons_holds (gate62 physical accepted) (cons_holds (gate63 physical accepted) (by intro gate member; cases member)))))))))))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
