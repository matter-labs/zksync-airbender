module
public import Proven.Compiler.NativeBindings.BlakeRound.Gates000
public import Proven.Compiler.NativeBindings.BlakeRound.Gates001
public import Proven.Compiler.NativeBindings.BlakeRound.Gates002
public import Proven.Compiler.NativeBindings.BlakeRound.Gates003
public import Proven.Compiler.NativeBindings.BlakeRound.Gates004
public import Proven.Compiler.NativeBindings.BlakeRound.Gates005
public import Proven.Compiler.NativeBindings.BlakeRound.Gates006
public import Proven.Compiler.NativeBindings.BlakeRound.Gates007
public import Proven.Compiler.NativeBindings.BlakeRound.Gates008
public import Proven.Compiler.NativeBindings.BlakeRound.Gates009
public import Proven.Compiler.NativeBindings.BlakeRound.Gates010
public import Proven.Compiler.NativeBindings.BlakeRound.Gates011
public import Proven.Compiler.NativeBindings.BlakeRound.Gates012
public import Proven.Compiler.NativeBindings.BlakeRound.Gates013
public import Proven.Compiler.NativeBindings.BlakeRound.Gates014
public import Proven.Compiler.NativeBindings.BlakeRound.Gates015
public import Proven.Compiler.NativeBindings.BlakeRound.Gates016
public import Proven.Compiler.NativeBindings.BlakeRound.Gates017
public import Proven.Compiler.NativeBindings.BlakeRound.Gates018
public import Proven.Compiler.NativeBindings.BlakeRound.Gates019
public import Proven.Compiler.NativeBindings.BlakeRound.Placement000
public import Proven.Compiler.NativeBindings.BlakeRound.Placement001
public import Proven.Compiler.NativeBindings.BlakeRound.Placement002
public import Proven.Compiler.NativeBindings.BlakeRound.Placement003
public import Proven.Compiler.NativeBindings.BlakeRound.Placement004
public import Proven.Compiler.NativeBindings.BlakeRound.Placement005
public import Proven.Compiler.NativeBindings.BlakeRound.Placement006
public import Proven.Compiler.NativeBindings.BlakeRound.Placement007
public import Proven.Compiler.NativeBindings.BlakeRound.Placement008
public import Proven.Compiler.NativeBindings.BlakeRound.Placement009
public import Proven.Compiler.NativeBindings.BlakeRound.Placement010
public import Proven.Compiler.NativeBindings.BlakeRound.Placement011
public import Proven.Compiler.NativeBindings.BlakeRound.Placement012
public import Proven.Compiler.NativeBindings.BlakeRound.Placement013
public import Proven.Compiler.NativeBindings.BlakeRound.Placement014
public import Proven.Compiler.NativeBindings.BlakeRound.Placement015
public import Proven.Compiler.NativeBindings.BlakeRound.Placement016
public import Proven.Compiler.NativeBindings.BlakeRound.Placement017
public import Proven.Compiler.NativeBindings.BlakeRound.Placement018
public import Proven.Compiler.NativeBindings.BlakeRound.Placement019
public import Proven.Compiler.NativeBindings.BlakeRound.Placement020
public import Proven.Compiler.NativeBindings.BlakeRound.Placement021
public import Proven.Compiler.NativeBindings.BlakeRound.Placement022
public import Proven.Compiler.NativeBindings.BlakeRound.Placement023
public import Proven.Compiler.NativeBindings.BlakeRound.Placement024
public import Proven.Compiler.NativeBindings.BlakeRound.Placement025
public import Proven.Compiler.NativeBindings.BlakeRound.Placement026
public import Proven.Compiler.NativeBindings.BlakeRound.Placement027
public import Proven.Compiler.NativeBindings.BlakeRound.Placement028
public import Proven.Compiler.NativeBindings.BlakeRound.Placement029
public import Proven.Compiler.NativeBindings.BlakeRound.Placement030
public import Proven.Compiler.NativeBindings.BlakeRound.Placement031

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.BlakeRound
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- Native acceptance supplies the complete checked arithmetic gate list. -/
theorem scalar_gates (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates,
      gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (append_holds (gates000 physical accepted) (append_holds (gates001 physical accepted) (append_holds (gates002 physical accepted) (append_holds (gates003 physical accepted) (append_holds (gates004 physical accepted) (append_holds (gates005 physical accepted) (append_holds (gates006 physical accepted) (append_holds (gates007 physical accepted) (append_holds (gates008 physical accepted) (append_holds (gates009 physical accepted) (append_holds (gates010 physical accepted) (append_holds (gates011 physical accepted) (append_holds (gates012 physical accepted) (append_holds (gates013 physical accepted) (append_holds (gates014 physical accepted) (append_holds (gates015 physical accepted) (append_holds (gates016 physical accepted) (append_holds (gates017 physical accepted) (append_holds (gates018 physical accepted) (append_holds (gates019 physical accepted) (by intro gate member; cases member)))))))))))))))))))))

/-- Public placement agreement supplies all variables used by the description. -/
theorem environment (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.BlakeRound.imported.circuit physical logical) :
    ∀ index < 763,
      (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get index = logical index := by
  have all : ∀ index ∈ List.range 763,
      (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
    (append_placements (placements000 physical logical agreement) (append_placements (placements001 physical logical agreement) (append_placements (placements002 physical logical agreement) (append_placements (placements003 physical logical agreement) (append_placements (placements004 physical logical agreement) (append_placements (placements005 physical logical agreement) (append_placements (placements006 physical logical agreement) (append_placements (placements007 physical logical agreement) (append_placements (placements008 physical logical agreement) (append_placements (placements009 physical logical agreement) (append_placements (placements010 physical logical agreement) (append_placements (placements011 physical logical agreement) (append_placements (placements012 physical logical agreement) (append_placements (placements013 physical logical agreement) (append_placements (placements014 physical logical agreement) (append_placements (placements015 physical logical agreement) (append_placements (placements016 physical logical agreement) (append_placements (placements017 physical logical agreement) (append_placements (placements018 physical logical agreement) (append_placements (placements019 physical logical agreement) (append_placements (placements020 physical logical agreement) (append_placements (placements021 physical logical agreement) (append_placements (placements022 physical logical agreement) (append_placements (placements023 physical logical agreement) (append_placements (placements024 physical logical agreement) (append_placements (placements025 physical logical agreement) (append_placements (placements026 physical logical agreement) (append_placements (placements027 physical logical agreement) (append_placements (placements028 physical logical agreement) (append_placements (placements029 physical logical agreement) (append_placements (placements030 physical logical agreement) (append_placements (placements031 physical logical agreement) (by intro index member; cases member)))))))))))))))))))))))))))))))))
  intro index bound
  exact all index (List.mem_range.mpr bound)

/-- The checked Clean expressions are the actual imported structured statements. -/
theorem equations : Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.expressions.map FlatOperation.assert = Circuit.equations Airbender.Compiler.Captures.BlakeRound.imported.circuit := by
  kernel_rfl

/-- Native cached arithmetic preserves the public constraint description. -/
theorem arithmetic : BlakeRoundCachedArithmeticClaim := by
  intro physical logical accepted agreement
  rw [← equations]
  exact assertions_transport Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.expressions _ _ 763 Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.scopeChecked
    (environment physical logical agreement)
    (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.arithmetic_preserved physical (Verification.environment logical).data (scalar_gates physical accepted))
end Airbender.Compiler.NativeBindings.BlakeRound
