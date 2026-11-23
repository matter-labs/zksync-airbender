module
public import Proven.Compiler.NativeBindings.BlakeRound.Gates023Part0
public import Proven.Compiler.NativeBindings.BlakeRound.Gates023Part1
public import Proven.Compiler.NativeBindings.BlakeRound.Gates023Part2
public import Proven.Compiler.NativeBindings.BlakeRound.Gates023Part3
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

/-- This batch retains every native scalar equation at these positions. -/
theorem gates023 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate184, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate185, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate186, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate187, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate188, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate189, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate190, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate191], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate184 physical accepted) (cons_holds (gate185 physical accepted) (cons_holds (gate186 physical accepted) (cons_holds (gate187 physical accepted) (cons_holds (gate188 physical accepted) (cons_holds (gate189 physical accepted) (cons_holds (gate190 physical accepted) (cons_holds (gate191 physical accepted) (by intro gate member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
