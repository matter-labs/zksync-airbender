module
public import Proven.Compiler.NativeBindings.BlakeRound.Gates024Part0
public import Proven.Compiler.NativeBindings.BlakeRound.Gates024Part1
public import Proven.Compiler.NativeBindings.BlakeRound.Gates024Part2
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
theorem gates024 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate192, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate193, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate194, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate195, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate196, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate197, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate198, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate199], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate192 physical accepted) (cons_holds (gate193 physical accepted) (cons_holds (gate194 physical accepted) (cons_holds (gate195 physical accepted) (cons_holds (gate196 physical accepted) (cons_holds (gate197 physical accepted) (cons_holds (gate198 physical accepted) (cons_holds (gate199 physical accepted) (by intro gate member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
