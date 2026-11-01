import Airbender.Proofs.GKRProtocol.CleanArguments
import Airbender.Proofs.GKRProtocol.NumericFunctionalBaseChecks

namespace Airbender.Compiler.NumericCleanArgumentChecks
set_option warningAsError true
open NumericFunctionalBaseChecks

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

def ofNative (expression : _root_.Expression Source.BaseField)
    (placement : Nat → Fin n) (fullBank : WireBank n)
    (native : Expression m Source.BaseField) (nativeBank : WireBank m) : Typed n babyBearModulus :=
  ⟨native.polynomial.flatMap (fun term => term.2.map (fun wire =>
      ⟨nativeBank.address wire, fullBank.address (fullBank.placement (nativeBank.address wire)), true⟩)),
    CleanExpression.polynomial placement expression,
    rename (fullBank.placement ∘ nativeBank.address) native.polynomial⟩

theorem address_decide (left right : GKRAddress) : addressEqual left right = decide (left = right) := by
  apply Bool.eq_iff_iff.mpr
  simp only [addressEqual_iff, decide_eq_true_eq]

theorem ofNative_check (expression : _root_.Expression Source.BaseField)
    (placement : Nat → Fin n) (fullBank : WireBank n)
    (native : Expression m Source.BaseField) (nativeBank : WireBank m) :
    (ofNative expression placement fullBank native nativeBank).check =
      CleanExpression.nativeCheck expression placement fullBank native nativeBank := by
  simp only [Typed.check, ofNative, CleanExpression.nativeCheck, List.all_flatMap,
    List.all_map, Function.comp_def, TypedPort.check, Bool.and_true, address_decide]

end Airbender.Compiler.NumericCleanArgumentChecks
