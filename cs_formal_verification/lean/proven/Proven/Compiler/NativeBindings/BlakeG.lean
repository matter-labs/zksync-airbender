module
public import Proven.Compiler.NativeBindings.BlakeG.Gates000
public import Proven.Compiler.NativeBindings.BlakeG.Gates001
public import Proven.Compiler.NativeBindings.BlakeG.Gates002
public import Proven.Compiler.NativeBindings.BlakeG.Gates003
public import Proven.Compiler.NativeBindings.BlakeG.Placement000
public import Proven.Compiler.NativeBindings.BlakeG.Placement001
public import Proven.Compiler.NativeBindings.BlakeG.Placement002
public import Proven.Compiler.NativeBindings.BlakeG.Placement003
public import Proven.Compiler.NativeBindings.BlakeG.Placement004

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.BlakeG
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- Native acceptance supplies the complete checked arithmetic gate list. -/
theorem scalar_gates (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeG.imported.circuit physical) :
    ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.artifact.gates,
      gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank.address) = 0 :=
  (append_holds (gates000 physical accepted) (append_holds (gates001 physical accepted) (append_holds (gates002 physical accepted) (append_holds (gates003 physical accepted) (by intro gate member; cases member)))))

/-- Public placement agreement supplies all variables used by the description. -/
theorem environment (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeG.imported.circuit physical logical) :
    ∀ index < 112,
      (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical (Verification.environment logical).data).get index = logical index := by
  have all : ∀ index ∈ List.range 112,
      (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
    (append_placements (placements000 physical logical agreement) (append_placements (placements001 physical logical agreement) (append_placements (placements002 physical logical agreement) (append_placements (placements003 physical logical agreement) (append_placements (placements004 physical logical agreement) (by intro index member; cases member))))))
  intro index bound
  exact all index (List.mem_range.mpr bound)

/-- The checked Clean expressions are the actual imported structured statements. -/
theorem equations : Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.expressions.map FlatOperation.assert = Circuit.equations Airbender.Compiler.Captures.BlakeG.imported.circuit := by
  kernel_rfl

/-- Native cached arithmetic preserves the public constraint description. -/
theorem arithmetic : BlakeGCachedArithmeticClaim := by
  intro physical logical accepted agreement
  rw [← equations]
  exact assertions_transport Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.expressions _ _ 112 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.scopeChecked
    (environment physical logical agreement)
    (Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.arithmetic_preserved physical (Verification.environment logical).data (scalar_gates physical accepted))
end Airbender.Compiler.NativeBindings.BlakeG
