module
public import Proven.Compiler.NativeBindings.Keccak.Gates000
public import Proven.Compiler.NativeBindings.Keccak.Gates001
public import Proven.Compiler.NativeBindings.Keccak.Gates002
public import Proven.Compiler.NativeBindings.Keccak.Gates003
public import Proven.Compiler.NativeBindings.Keccak.Gates004
public import Proven.Compiler.NativeBindings.Keccak.Gates005
public import Proven.Compiler.NativeBindings.Keccak.Gates006
public import Proven.Compiler.NativeBindings.Keccak.Gates007
public import Proven.Compiler.NativeBindings.Keccak.Gates008
public import Proven.Compiler.NativeBindings.Keccak.Gates009
public import Proven.Compiler.NativeBindings.Keccak.Gates010
public import Proven.Compiler.NativeBindings.Keccak.Gates011
public import Proven.Compiler.NativeBindings.Keccak.Gates012
public import Proven.Compiler.NativeBindings.Keccak.Gates013
public import Proven.Compiler.NativeBindings.Keccak.Placement000
public import Proven.Compiler.NativeBindings.Keccak.Placement001
public import Proven.Compiler.NativeBindings.Keccak.Placement002
public import Proven.Compiler.NativeBindings.Keccak.Placement003
public import Proven.Compiler.NativeBindings.Keccak.Placement004
public import Proven.Compiler.NativeBindings.Keccak.Placement005
public import Proven.Compiler.NativeBindings.Keccak.Placement006
public import Proven.Compiler.NativeBindings.Keccak.Placement007
public import Proven.Compiler.NativeBindings.Keccak.Placement008
public import Proven.Compiler.NativeBindings.Keccak.Placement009
public import Proven.Compiler.NativeBindings.Keccak.Placement010
public import Proven.Compiler.NativeBindings.Keccak.Placement011

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.Keccak
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- Native acceptance supplies the complete checked arithmetic gate list. -/
theorem scalar_gates (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates,
      gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 :=
  (append_holds (gates000 physical accepted) (append_holds (gates001 physical accepted) (append_holds (gates002 physical accepted) (append_holds (gates003 physical accepted) (append_holds (gates004 physical accepted) (append_holds (gates005 physical accepted) (append_holds (gates006 physical accepted) (append_holds (gates007 physical accepted) (append_holds (gates008 physical accepted) (append_holds (gates009 physical accepted) (append_holds (gates010 physical accepted) (append_holds (gates011 physical accepted) (append_holds (gates012 physical accepted) (append_holds (gates013 physical accepted) (by intro gate member; cases member)))))))))))))))

/-- Public placement agreement supplies all variables used by the description. -/
theorem environment (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    ∀ index < 266,
      (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get index = logical index := by
  have all : ∀ index ∈ List.range 266,
      (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
    (append_placements (placements000 physical logical agreement) (append_placements (placements001 physical logical agreement) (append_placements (placements002 physical logical agreement) (append_placements (placements003 physical logical agreement) (append_placements (placements004 physical logical agreement) (append_placements (placements005 physical logical agreement) (append_placements (placements006 physical logical agreement) (append_placements (placements007 physical logical agreement) (append_placements (placements008 physical logical agreement) (append_placements (placements009 physical logical agreement) (append_placements (placements010 physical logical agreement) (append_placements (placements011 physical logical agreement) (by intro index member; cases member)))))))))))))
  intro index bound
  exact all index (List.mem_range.mpr bound)

/-- The checked Clean expressions are the actual imported structured statements. -/
theorem equations : Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.expressions.map FlatOperation.assert = Circuit.equations Airbender.Compiler.Captures.Keccak.imported.circuit := by
  kernel_rfl

/-- Native cached arithmetic preserves the public constraint description. -/
theorem arithmetic : KeccakCachedArithmeticClaim := by
  intro physical logical accepted agreement
  rw [← equations]
  exact assertions_transport Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.expressions _ _ 266 Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.scopeChecked
    (environment physical logical agreement)
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.arithmetic_preserved physical (Verification.environment logical).data (scalar_gates physical accepted))
end Airbender.Compiler.NativeBindings.Keccak
