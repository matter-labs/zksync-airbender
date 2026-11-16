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

/-- The actual native sparse relation supplies gate 40. -/
theorem gate40 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate40.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate40.check = true :=
    all_at (index := 40) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate40) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[128]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry128 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate40 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry128).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry128).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate40, Expression.value, Function.comp_apply, coordinate2, coordinate651, coordinate716, coordinate809]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨128, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry128 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 41. -/
theorem gate41 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate41.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate41.check = true :=
    all_at (index := 41) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate41) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[129]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry129 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate41 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry129).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry129).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate41, Expression.value, Function.comp_apply, coordinate1, coordinate652, coordinate717, coordinate810]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨129, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry129 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 42. -/
theorem gate42 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate42.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate42.check = true :=
    all_at (index := 42) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate42) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[130]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry130 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate42 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry130).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry130).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate42, Expression.value, Function.comp_apply, coordinate2, coordinate652, coordinate718, coordinate811]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨130, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry130 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 43. -/
theorem gate43 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate43.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate43.check = true :=
    all_at (index := 43) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate43) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[131]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry131 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate43 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry131).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry131).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate43, Expression.value, Function.comp_apply, coordinate1, coordinate653, coordinate719, coordinate812]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨131, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry131 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 44. -/
theorem gate44 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate44.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate44.check = true :=
    all_at (index := 44) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate44) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[132]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry132 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate44 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry132).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry132).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate44, Expression.value, Function.comp_apply, coordinate2, coordinate653, coordinate720, coordinate813]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨132, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry132 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 45. -/
theorem gate45 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate45.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate45.check = true :=
    all_at (index := 45) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate45) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[133]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry133 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate45 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry133).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry133).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate45, Expression.value, Function.comp_apply, coordinate1, coordinate654, coordinate721, coordinate814]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨133, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry133 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 46. -/
theorem gate46 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate46.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate46.check = true :=
    all_at (index := 46) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate46) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[134]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry134 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate46 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry134).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry134).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate46, Expression.value, Function.comp_apply, coordinate2, coordinate654, coordinate722, coordinate815]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨134, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry134 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 47. -/
theorem gate47 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate47.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate47.check = true :=
    all_at (index := 47) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate47) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[135]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry135 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate47 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry135).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry135).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate47, Expression.value, Function.comp_apply, coordinate1, coordinate655, coordinate723, coordinate816]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨135, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry135 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- This batch retains every native scalar equation at these positions. -/
theorem gates002 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate32, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate33, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate34, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate35, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate36, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate37, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate38, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate39, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate40, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate41, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate42, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate43, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate44, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate45, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate46, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate47], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate32 physical accepted) (cons_holds (gate33 physical accepted) (cons_holds (gate34 physical accepted) (cons_holds (gate35 physical accepted) (cons_holds (gate36 physical accepted) (cons_holds (gate37 physical accepted) (cons_holds (gate38 physical accepted) (cons_holds (gate39 physical accepted) (cons_holds (gate40 physical accepted) (cons_holds (gate41 physical accepted) (cons_holds (gate42 physical accepted) (cons_holds (gate43 physical accepted) (cons_holds (gate44 physical accepted) (cons_holds (gate45 physical accepted) (cons_holds (gate46 physical accepted) (cons_holds (gate47 physical accepted) (by intro gate member; cases member)))))))))))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
