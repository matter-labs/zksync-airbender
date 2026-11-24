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

/-- The actual native sparse relation supplies gate 32. -/
theorem gate32 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate32.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate32.check = true :=
    all_at (index := 32) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate32) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[120]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry120 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate32 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry120).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry120).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate32, Expression.value, Function.comp_apply, coordinate2, coordinate647, coordinate708, coordinate801]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨120, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry120 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 33. -/
theorem gate33 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate33.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate33.check = true :=
    all_at (index := 33) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate33) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[121]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry121 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate33 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry121).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry121).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate33, Expression.value, Function.comp_apply, coordinate1, coordinate648, coordinate709, coordinate802]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨121, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry121 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 34. -/
theorem gate34 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate34.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate34.check = true :=
    all_at (index := 34) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate34) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[122]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry122 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate34 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry122).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry122).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate34, Expression.value, Function.comp_apply, coordinate2, coordinate648, coordinate710, coordinate803]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨122, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry122 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 35. -/
theorem gate35 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate35.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate35.check = true :=
    all_at (index := 35) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate35) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[123]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry123 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate35 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry123).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry123).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate35, Expression.value, Function.comp_apply, coordinate1, coordinate649, coordinate711, coordinate804]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨123, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry123 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 36. -/
theorem gate36 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate36.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate36.check = true :=
    all_at (index := 36) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate36) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[124]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry124 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate36 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry124).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry124).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate36, Expression.value, Function.comp_apply, coordinate2, coordinate649, coordinate712, coordinate805]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨124, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry124 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 37. -/
theorem gate37 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate37.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate37.check = true :=
    all_at (index := 37) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate37) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[125]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry125 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate37 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry125).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry125).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate37, Expression.value, Function.comp_apply, coordinate1, coordinate650, coordinate713, coordinate806]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨125, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry125 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 38. -/
theorem gate38 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate38.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate38.check = true :=
    all_at (index := 38) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate38) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[126]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry126 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate38 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry126).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry126).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate38, Expression.value, Function.comp_apply, coordinate2, coordinate650, coordinate714, coordinate807]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨126, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry126 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 39. -/
theorem gate39 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate39.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate39.check = true :=
    all_at (index := 39) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate39) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[127]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry127 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate39 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry127).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry127).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate39, Expression.value, Function.comp_apply, coordinate1, coordinate651, coordinate715, coordinate808]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨127, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry127 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- This batch retains every native scalar equation at these positions. -/
theorem gates004 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate32, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate33, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate34, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate35, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate36, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate37, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate38, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate39], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate32 physical accepted) (cons_holds (gate33 physical accepted) (cons_holds (gate34 physical accepted) (cons_holds (gate35 physical accepted) (cons_holds (gate36 physical accepted) (cons_holds (gate37 physical accepted) (cons_holds (gate38 physical accepted) (cons_holds (gate39 physical accepted) (by intro gate member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
