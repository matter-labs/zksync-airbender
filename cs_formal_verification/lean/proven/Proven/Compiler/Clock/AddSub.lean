module
public import Proven.GKRProtocol.CleanLinksNative.AddSubCached
public import Proven.Compiler.Lookups.Ranges.AddSub
public import Proven.Compiler.Lookups.NativeHelpers
public import Proven.Compiler.ScopeChecks

@[expose] public section
namespace Airbender.Compiler.NativeClock.AddSub
open Airbender Airbender.Compiler Airbender.Trace NativeArithmetic
set_option warningAsError true
set_option maxRecDepth 65536

theorem lookup_inventory : FlatOperation.lookups (AddSub.clockConstraints (p := babyBearModulus)) =
    Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpressions.map Verification.range16 ++ Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpressions.map Trace.timestampLookup := by rfl

/-- Native equations and exact table matching imply every retained CPU clock constraint. -/
theorem physical (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → F) (data : ProverData F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .addSub)) physical)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .addSub))
      (NativeLookups.selectorsFor (.pooled .addSub)) physical (NativePublicSetup.rows initial program (.pooled .addSub))) :
    FlatOperation.ConstraintsHoldFlat
      (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (AddSub.clockConstraints (p := babyBearModulus)) := by
  let arithmetic := NativeBindings.AddSub.scalar_gates physical accepted
  have helpers := NativeHelpers.AddSub.bounded initial program physical accepted arguments
  apply CleanLinksNative.AddSubCached.retained_clock_constraints physical data arithmetic
  rw [lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (NativeRangeLookups.AddSub.range_lookup0 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.AddSub.range_lookup1 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.AddSub.range_lookup2 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.AddSub.range_lookup3 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.AddSub.range_lookup4 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.AddSub.range_lookup5 initial program physical data arithmetic arguments) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound0 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound1 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound2 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound3 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound4 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound5 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound6 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestamp_bound7 physical data arithmetic helpers)) PredicateChecks.nil))))))))))))))

/-- Checked placements transfer the complete native row into its logical witness interpretation. -/
theorem logical (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .addSub)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .addSub)) physical assignment)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .addSub))
      (NativeLookups.selectorsFor (.pooled .addSub)) physical (NativePublicSetup.rows initial program (.pooled .addSub))) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment assignment) (AddSub.clockConstraints (p := babyBearModulus)) := by
  apply NativeBridge.constraints_transport (AddSub.clockConstraints (p := babyBearModulus))
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical (Verification.environment assignment).data)
    (Verification.environment assignment) 48
    (NativeBridge.ScopeChecks.addSub_scope)
    (NativeBindings.AddSub.environment physical assignment agreement) rfl
  exact NativeClock.AddSub.physical initial program physical _ accepted arguments

end Airbender.Compiler.NativeClock.AddSub
