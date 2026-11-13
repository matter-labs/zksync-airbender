module
public import Proven.Compiler.NativeBindings.WordMemory.Gates000
public import Proven.Compiler.NativeBindings.WordMemory.Gates001
public import Proven.Compiler.NativeBindings.WordMemory.Gates002
public import Proven.Compiler.NativeBindings.WordMemory.Placement000
public import Proven.Compiler.NativeBindings.WordMemory.Placement001
public import Proven.Compiler.NativeBindings.WordMemory.Placement002

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.WordMemory
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- Native acceptance supplies the complete checked arithmetic gate list. -/
theorem scalar_gates (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.artifact.gates,
      gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 :=
  (append_holds (gates000 physical accepted) (append_holds (gates001 physical accepted) (append_holds (gates002 physical accepted) (by intro gate member; cases member))))

/-- Public placement agreement supplies all variables used by the description. -/
theorem environment (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.WordMemory.imported.circuit physical logical) :
    ∀ index < 52,
      (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical (Verification.environment logical).data).get index = logical index := by
  have all : ∀ index ∈ List.range 52,
      (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
    (append_placements (placements000 physical logical agreement) (append_placements (placements001 physical logical agreement) (append_placements (placements002 physical logical agreement) (by intro index member; cases member))))
  intro index bound
  exact all index (List.mem_range.mpr bound)

/-- The checked Clean expressions are the actual imported structured statements. -/
theorem equations : Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.expressions.map FlatOperation.assert = Circuit.equations Airbender.Compiler.Captures.WordMemory.imported.circuit := by
  kernel_rfl

/-- Native cached arithmetic preserves the public constraint description. -/
theorem arithmetic : WordMemoryCachedArithmeticClaim := by
  intro physical logical accepted agreement
  rw [← equations]
  exact assertions_transport Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.expressions _ _ 52 Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.scopeChecked
    (environment physical logical agreement)
    (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.arithmetic_preserved physical (Verification.environment logical).data (scalar_gates physical accepted))
end Airbender.Compiler.NativeBindings.WordMemory
