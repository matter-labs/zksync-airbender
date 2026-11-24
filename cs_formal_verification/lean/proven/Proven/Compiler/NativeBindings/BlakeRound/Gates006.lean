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

/-- This batch retains every native scalar equation at these positions. -/
theorem gates006 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate48, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate49, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate50, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate51, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate52, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate53, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate54, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate55], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate48 physical accepted) (cons_holds (gate49 physical accepted) (cons_holds (gate50 physical accepted) (cons_holds (gate51 physical accepted) (cons_holds (gate52 physical accepted) (cons_holds (gate53 physical accepted) (cons_holds (gate54 physical accepted) (cons_holds (gate55 physical accepted) (by intro gate member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
