module
public import Proven.Compiler.NativeBindings.BlakeRound.Gates020Part0
public import Proven.Compiler.NativeBindings.BlakeRound.Gates020Part1
public import Proven.Compiler.NativeBindings.BlakeRound.Gates020Part2
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
theorem gates020 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate160, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate161, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate162, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate163, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate164, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate165, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate166, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate167], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate160 physical accepted) (cons_holds (gate161 physical accepted) (cons_holds (gate162 physical accepted) (cons_holds (gate163 physical accepted) (cons_holds (gate164 physical accepted) (cons_holds (gate165 physical accepted) (cons_holds (gate166 physical accepted) (cons_holds (gate167 physical accepted) (by intro gate member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
