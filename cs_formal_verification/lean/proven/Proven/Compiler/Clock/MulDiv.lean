module
public import Proven.GKRProtocol.CleanLinksNative.MulDivCached
public import Proven.Compiler.Lookups.Ranges.MulDiv
public import Proven.Compiler.Lookups.NativeHelpers
public import Proven.Compiler.ScopeChecks
public import Proven.Compiler.Lookups.Vectors.MulDiv

@[expose] public section
namespace Airbender.Compiler.NativeClock.MulDiv
open Airbender Airbender.Compiler Airbender.Trace NativeArithmetic
set_option warningAsError true
set_option maxRecDepth 65536

theorem lookup_inventory :
    FlatOperation.lookups (Airbender.MulDiv.clockConstraints (p := babyBearModulus)) =
    (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.rangeExpressions.map Verification.range16) ++ NativeVectorLookups.MulDiv.fixedLookups ++
      (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampExpressions.map Trace.timestampLookup) := by rfl


/-- Native equations and exact table matching imply every retained CPU clock constraint. -/
theorem physical (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → F) (data : ProverData F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .mulDiv)) physical)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .mulDiv))
      (NativeLookups.selectorsFor (.pooled .mulDiv)) physical (NativePublicSetup.rows initial program (.pooled .mulDiv))) :
    FlatOperation.ConstraintsHoldFlat
      (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) (MulDiv.clockConstraints (p := babyBearModulus)) := by
  let arithmetic := NativeBindings.MulDiv.scalar_gates physical accepted
  have helpers := NativeHelpers.MulDiv.bounded initial program physical accepted arguments
  apply CleanLinksNative.MulDivCached.retained_clock_constraints physical data arithmetic
  rw [lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (NativeRangeLookups.MulDiv.range_lookup0 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.MulDiv.range_lookup1 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.MulDiv.range_lookup2 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.MulDiv.range_lookup3 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.MulDiv.range_lookup4 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.MulDiv.range_lookup5 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.MulDiv.range_lookup6 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.MulDiv.range_lookup7 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.MulDiv.generic_lookup0 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.MulDiv.generic_lookup1 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.MulDiv.generic_lookup2 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.MulDiv.generic_lookup3 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.MulDiv.generic_lookup4 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.MulDiv.generic_lookup5 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.MulDiv.generic_lookup6 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.MulDiv.generic_lookup7 initial program physical data arithmetic arguments) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestamp_bound0 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestamp_bound1 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestamp_bound2 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestamp_bound3 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestamp_bound4 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestamp_bound5 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestamp_bound6 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.MulDivCached.native.timestamp_bound7 physical data arithmetic helpers)) PredicateChecks.nil))))))))))))))))))))))))

/-- Checked placements transfer the complete native row into its logical witness interpretation. -/
theorem logical (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .mulDiv)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .mulDiv)) physical assignment)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .mulDiv))
      (NativeLookups.selectorsFor (.pooled .mulDiv)) physical (NativePublicSetup.rows initial program (.pooled .mulDiv))) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment assignment) (MulDiv.clockConstraints (p := babyBearModulus)) := by
  apply NativeBridge.constraints_transport (MulDiv.clockConstraints (p := babyBearModulus))
    (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical (Verification.environment assignment).data)
    (Verification.environment assignment) 71
    (NativeBridge.ScopeChecks.mulDiv_scope)
    (NativeBindings.MulDiv.environment physical assignment agreement) rfl
  exact NativeClock.MulDiv.physical initial program physical _ accepted arguments

end Airbender.Compiler.NativeClock.MulDiv
