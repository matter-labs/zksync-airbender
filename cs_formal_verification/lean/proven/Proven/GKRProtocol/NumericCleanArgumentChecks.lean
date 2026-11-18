module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.CleanArguments
public import Proven.GKRProtocol.NumericFunctionalBaseChecks

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.NumericCleanArgumentChecks
open NumericFunctionalBaseChecks

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

def ofNative (expression : Airbender.Expression Source.BaseField)
    (placement : Nat → Fin n) (fullBank : WireBank n)
    (native : Expression m Source.BaseField) (nativeBank : WireBank m) : Typed n babyBearModulus :=
  ⟨native.polynomial.flatMap (fun term => term.2.map (fun wire =>
      ⟨nativeBank.address wire, fullBank.address (fullBank.placement (nativeBank.address wire)), true⟩)),
    CleanExpression.polynomial placement expression,
    rename (fullBank.placement ∘ nativeBank.address) native.polynomial⟩

theorem address_decide (left right : GKRAddress) : addressEqual left right = decide (left = right) := by
  apply Bool.eq_iff_iff.mpr
  simp only [addressEqual_iff, decide_eq_true_eq]

theorem ofNative_check (expression : Airbender.Expression Source.BaseField)
    (placement : Nat → Fin n) (fullBank : WireBank n)
    (native : Expression m Source.BaseField) (nativeBank : WireBank m) :
    (ofNative expression placement fullBank native nativeBank).check =
      CleanExpression.nativeCheck expression placement fullBank native nativeBank := by
  simp only [Typed.check, ofNative, CleanExpression.nativeCheck, List.all_flatMap,
    List.all_map, Function.comp_def, TypedPort.check, Bool.and_true, address_decide]

theorem checked_window {items : List α} {predicate : α → Bool}
    (checked : items.all predicate = true) (first width : Nat) :
    ((items.drop first).take width).all predicate = true := by
  apply List.all_eq_true.mpr
  intro item member
  exact List.all_eq_true.mp checked item
    (List.mem_of_mem_drop (List.mem_of_mem_take member))

end Airbender.Compiler.NumericCleanArgumentChecks
