module
public import Proven.Compiler.NativeBindings.BlakeRound.Gates022Part0
public import Proven.Compiler.NativeBindings.BlakeRound.Gates022Part1
public import Proven.Compiler.NativeBindings.BlakeRound.Gates022Part2
public import Proven.Compiler.NativeBindings.BlakeRound.Gates022Part3
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
theorem gates022 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate176, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate177, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate178, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate179, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate180, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate181, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate182, Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.gate183], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0 :=
  (cons_holds (gate176 physical accepted) (cons_holds (gate177 physical accepted) (cons_holds (gate178 physical accepted) (cons_holds (gate179 physical accepted) (cons_holds (gate180 physical accepted) (cons_holds (gate181 physical accepted) (cons_holds (gate182 physical accepted) (cons_holds (gate183 physical accepted) (by intro gate member; cases member)))))))))
end Airbender.Compiler.NativeBindings.BlakeRound
