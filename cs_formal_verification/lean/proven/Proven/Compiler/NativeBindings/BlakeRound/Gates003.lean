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

/-- The actual native sparse relation supplies gate 24. -/
theorem gate24 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate24.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate24.check = true :=
    all_at (index := 24) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate24) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[112]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry112 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate24 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry112).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry112).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate24, Expression.value, Function.comp_apply, coordinate2, coordinate643, coordinate700, coordinate793]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨112, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry112 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 25. -/
theorem gate25 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate25.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate25.check = true :=
    all_at (index := 25) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate25) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[113]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry113 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate25 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry113).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry113).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate25, Expression.value, Function.comp_apply, coordinate1, coordinate644, coordinate701, coordinate794]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨113, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry113 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 26. -/
theorem gate26 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate26.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate26.check = true :=
    all_at (index := 26) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate26) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[114]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry114 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate26 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry114).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry114).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate26, Expression.value, Function.comp_apply, coordinate2, coordinate644, coordinate702, coordinate795]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨114, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry114 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 27. -/
theorem gate27 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate27.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate27.check = true :=
    all_at (index := 27) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate27) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[115]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry115 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate27 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry115).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry115).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate27, Expression.value, Function.comp_apply, coordinate1, coordinate645, coordinate703, coordinate796]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨115, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry115 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 28. -/
theorem gate28 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate28.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate28.check = true :=
    all_at (index := 28) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate28) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[116]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry116 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate28 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry116).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry116).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate28, Expression.value, Function.comp_apply, coordinate2, coordinate645, coordinate704, coordinate797]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨116, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry116 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 29. -/
theorem gate29 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate29.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate29.check = true :=
    all_at (index := 29) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate29) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[117]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry117 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate29 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry117).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry117).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate29, Expression.value, Function.comp_apply, coordinate1, coordinate646, coordinate705, coordinate798]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨117, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry117 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 30. -/
theorem gate30 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate30.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate30.check = true :=
    all_at (index := 30) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate30) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[118]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry118 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate30 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry118).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry118).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate30, Expression.value, Function.comp_apply, coordinate2, coordinate646, coordinate706, coordinate799]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨118, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry118 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 31. -/
theorem gate31 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate31.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate31.check = true :=
    all_at (index := 31) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate31) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[119]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry119 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate31 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry119).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry119).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate31, Expression.value, Function.comp_apply, coordinate1, coordinate647, coordinate707, coordinate800]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨119, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry119 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- This batch retains every native scalar equation at these positions. -/
theorem gates003 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate24, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate25, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate26, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate27, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate28, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate29, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate30, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate31], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate24 physical accepted) (cons_holds (gate25 physical accepted) (cons_holds (gate26 physical accepted) (cons_holds (gate27 physical accepted) (cons_holds (gate28 physical accepted) (cons_holds (gate29 physical accepted) (cons_holds (gate30 physical accepted) (cons_holds (gate31 physical accepted) (by intro gate member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
