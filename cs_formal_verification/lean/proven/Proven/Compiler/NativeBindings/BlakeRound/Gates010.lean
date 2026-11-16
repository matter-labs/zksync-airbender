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

/-- The actual native sparse relation supplies gate 80. -/
theorem gate80 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate80.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate80.check = true :=
    all_at (index := 80) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate80) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[168]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry168 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate80 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry168).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry168).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate80, Expression.value, Function.comp_apply, coordinate2, coordinate671, coordinate756, coordinate849]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨168, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry168 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 81. -/
theorem gate81 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate81.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate81.check = true :=
    all_at (index := 81) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate81) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[169]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry169 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate81 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry169).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry169).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate81, Expression.value, Function.comp_apply, coordinate1, coordinate672, coordinate757, coordinate850]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨169, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry169 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 82. -/
theorem gate82 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate82.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate82.check = true :=
    all_at (index := 82) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate82) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[170]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry170 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate82 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry170).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry170).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate82, Expression.value, Function.comp_apply, coordinate2, coordinate672, coordinate758, coordinate851]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨170, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry170 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 83. -/
theorem gate83 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate83.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate83.check = true :=
    all_at (index := 83) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate83) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[171]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry171 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate83 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry171).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry171).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate83, Expression.value, Function.comp_apply, coordinate1, coordinate673, coordinate759, coordinate852]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨171, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry171 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 84. -/
theorem gate84 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate84.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate84.check = true :=
    all_at (index := 84) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate84) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[172]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry172 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate84 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry172).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry172).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate84, Expression.value, Function.comp_apply, coordinate2, coordinate673, coordinate760, coordinate853]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨172, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry172 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 85. -/
theorem gate85 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate85.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate85.check = true :=
    all_at (index := 85) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate85) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[173]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry173 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate85 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry173).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry173).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate85, Expression.value, Function.comp_apply, coordinate1, coordinate674, coordinate761, coordinate854]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨173, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry173 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 86. -/
theorem gate86 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate86.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate86.check = true :=
    all_at (index := 86) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate86) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[174]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry174 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate86 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry174).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry174).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate86, Expression.value, Function.comp_apply, coordinate2, coordinate674, coordinate762, coordinate855]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨174, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry174 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- The actual native sparse relation supplies gate 87. -/
theorem gate87 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate87.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate87.check = true :=
    all_at (index := 87) (value := Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate87) scalar_gate_data_checked (by cbv)
  have captured : ((Airbender.Compiler.Captures.BlakeRound.imported.circuit).layers[0]'(by decide)).cached_relations[175]'(by decide) = Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry175 :=
    entry_of_binding (by decide) layer0_caches (by cbv)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate87 (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) =
      (Clause.cache (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry175).1 (Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry175).2).residual physical := by
    simp only [sparseResidual, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate87, Expression.value, Function.comp_apply, coordinate3, coordinate856]
    rfl
  have acceptedEntry := cache_at_literal accepted ⟨0, by decide⟩ ⟨175, by decide⟩ Airbender.Compiler.Captures.BlakeRound.importedLayer0CachesEntry175 captured
  exact (sparse_checked checked _).symm.trans (binding.trans acceptedEntry)

/-- This batch retains every native scalar equation at these positions. -/
theorem gates010 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate80, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate81, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate82, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate83, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate84, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate85, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate86, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate87], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate80 physical accepted) (cons_holds (gate81 physical accepted) (cons_holds (gate82 physical accepted) (cons_holds (gate83 physical accepted) (cons_holds (gate84 physical accepted) (cons_holds (gate85 physical accepted) (cons_holds (gate86 physical accepted) (cons_holds (gate87 physical accepted) (by intro gate member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
