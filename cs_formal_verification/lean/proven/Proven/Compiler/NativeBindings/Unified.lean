module
public import Proven.Compiler.NativeBindings.Unified.Gates000
public import Proven.Compiler.NativeBindings.Unified.Gates001
public import Proven.Compiler.NativeBindings.Unified.Gates002
public import Proven.Compiler.NativeBindings.Unified.Gates003
public import Proven.Compiler.NativeBindings.Unified.Gates004
public import Proven.Compiler.NativeBindings.Unified.Gates005
public import Proven.Compiler.NativeBindings.Unified.Gates006
public import Proven.Compiler.NativeBindings.Unified.Gates007
public import Proven.Compiler.NativeBindings.Unified.Gates008
public import Proven.Compiler.NativeBindings.Unified.Placement000
public import Proven.Compiler.NativeBindings.Unified.Placement001
public import Proven.Compiler.NativeBindings.Unified.Placement002
public import Proven.Compiler.NativeBindings.Unified.Placement003
public import Proven.Compiler.NativeBindings.Unified.Placement004
public import Proven.Compiler.NativeBindings.Unified.Placement005

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.Unified
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- Native acceptance supplies the complete checked arithmetic gate list. -/
theorem scalar_gates (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Unified.imported.circuit physical) :
    ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates,
      gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0 :=
  (append_holds (gates000 physical accepted) (append_holds (gates001 physical accepted) (append_holds (gates002 physical accepted) (append_holds (gates003 physical accepted) (append_holds (gates004 physical accepted) (append_holds (gates005 physical accepted) (append_holds (gates006 physical accepted) (append_holds (gates007 physical accepted) (append_holds (gates008 physical accepted) (by intro gate member; cases member))))))))))

/-- Public placement agreement supplies all variables used by the description. -/
theorem environment (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Unified.imported.circuit physical logical) :
    ∀ index < 137,
      (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical (Verification.environment logical).data).get index = logical index := by
  have all : ∀ index ∈ List.range 137,
      (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
    (append_placements (placements000 physical logical agreement) (append_placements (placements001 physical logical agreement) (append_placements (placements002 physical logical agreement) (append_placements (placements003 physical logical agreement) (append_placements (placements004 physical logical agreement) (append_placements (placements005 physical logical agreement) (by intro index member; cases member)))))))
  intro index bound
  exact all index (List.mem_range.mpr bound)

/-- The checked Clean expressions are the actual imported structured statements. -/
theorem equations : Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.expressions.map FlatOperation.assert = Circuit.equations Airbender.Compiler.Captures.Unified.imported.circuit := by
  kernel_rfl

/-- Native cached arithmetic preserves the public constraint description. -/
theorem arithmetic : UnifiedCachedArithmeticClaim := by
  intro physical logical accepted agreement
  rw [← equations]
  exact assertions_transport Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.expressions _ _ 137 Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.scopeChecked
    (environment physical logical agreement)
    (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.arithmetic_preserved physical (Verification.environment logical).data (scalar_gates physical accepted))
end Airbender.Compiler.NativeBindings.Unified
