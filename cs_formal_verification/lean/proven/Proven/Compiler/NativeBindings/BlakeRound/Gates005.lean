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
theorem gates005 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate40, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate41, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate42, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate43, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate44, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate45, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate46, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate47], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate40 physical accepted) (cons_holds (gate41 physical accepted) (cons_holds (gate42 physical accepted) (cons_holds (gate43 physical accepted) (cons_holds (gate44 physical accepted) (cons_holds (gate45 physical accepted) (cons_holds (gate46 physical accepted) (cons_holds (gate47 physical accepted) (by intro gate member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
