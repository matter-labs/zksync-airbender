module
public import Proven.Compiler.NativeBindings.BlakeRound.Gates021Part0
public import Proven.Compiler.NativeBindings.BlakeRound.Gates021Part1
public import Proven.Compiler.NativeBindings.BlakeRound.Gates021Part2
public import Proven.Compiler.NativeBindings.BlakeRound.Gates021Part3
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
theorem gates021 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate168, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate169, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate170, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate171, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate172, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate173, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate174, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate175], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate168 physical accepted) (cons_holds (gate169 physical accepted) (cons_holds (gate170 physical accepted) (cons_holds (gate171 physical accepted) (cons_holds (gate172 physical accepted) (cons_holds (gate173 physical accepted) (cons_holds (gate174 physical accepted) (cons_holds (gate175 physical accepted) (by intro gate member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
