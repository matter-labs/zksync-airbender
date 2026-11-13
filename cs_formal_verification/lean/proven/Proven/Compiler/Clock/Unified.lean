module
public import Proven.GKRProtocol.CleanLinksNative.UnifiedCached
public import Proven.Compiler.Lookups.Ranges.Unified
public import Proven.Compiler.Lookups.NativeHelpers
public import Proven.Compiler.ScopeChecks
public import Proven.Compiler.Lookups.Vectors.Unified

@[expose] public section
namespace Airbender.Compiler.NativeClock.Unified
open Airbender Airbender.Compiler Airbender.Trace NativeArithmetic
set_option warningAsError true
set_option maxRecDepth 65536

theorem lookup_inventory (initial : RV.State) : FlatOperation.lookups (UnifiedReduced.clockConstraints (p := babyBearModulus) (UnifiedReduced.Setup.tableRV (p := babyBearModulus) initial)) =
    Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.rangeExpressions.map Verification.range16 ++ Airbender.Compiler.CleanGenericArgumentsNative.UnifiedCached.native.genericExpressions.map (fun entry => Lookup.mk (UnifiedReduced.Setup.tableRV (p := babyBearModulus) initial).toRaw entry) ++ Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampExpressions.map Trace.timestampLookup := by rfl

/-- Native equations and exact table matching imply every retained CPU clock constraint. -/
theorem physical (initial : RV.State) (program : List RVMachineProgramEntry)
    {actual : ProgramLookupRows} (bound : NativePublicSetup.Bound initial program actual)
    (physical : GKRAddress → F) (data : ProverData F)
    (accepted : Holds (NativeLookups.circuitFor .unified) physical)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor .unified)
      (NativeLookups.selectorsFor .unified) physical (NativePublicSetup.rows initial program .unified)) :
    FlatOperation.ConstraintsHoldFlat
      (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) (UnifiedReduced.clockConstraints (p := babyBearModulus) (UnifiedReduced.Setup.tableRV (p := babyBearModulus) initial)) := by
  let arithmetic := NativeBindings.Unified.scalar_gates physical accepted
  have helpers := NativeHelpers.Unified.bounded initial program physical accepted arguments
  apply CleanLinksNative.UnifiedCached.retained_clock_constraints (UnifiedReduced.Setup.tableRV (p := babyBearModulus) initial) physical data arithmetic
  rw [lookup_inventory initial]
  exact PredicateChecks.all (PredicateChecks.cons (NativeRangeLookups.Unified.range_lookup0 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.Unified.range_lookup1 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.Unified.range_lookup2 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.Unified.range_lookup3 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.Unified.range_lookup4 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.Unified.range_lookup5 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.Unified.range_lookup6 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.Unified.range_lookup7 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.Unified.range_lookup8 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.Unified.range_lookup9 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.Unified.range_lookup10 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.Unified.range_lookup11 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.Unified.range_lookup12 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.Unified.generic_lookup0 initial program bound physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.Unified.generic_lookup1 initial program bound physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.Unified.generic_lookup2 initial program bound physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.Unified.generic_lookup3 initial program bound physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.Unified.generic_lookup4 initial program bound physical data arithmetic arguments) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestamp_bound0 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestamp_bound1 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestamp_bound2 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestamp_bound3 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestamp_bound4 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestamp_bound5 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestamp_bound6 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.UnifiedCached.native.timestamp_bound7 physical data arithmetic helpers)) PredicateChecks.nil))))))))))))))))))))))))))

/-- Checked placements transfer the complete native row into its logical witness interpretation. -/
theorem logical (initial : RV.State) (program : List RVMachineProgramEntry)
    {actual : ProgramLookupRows} (bound : NativePublicSetup.Bound initial program actual)
    (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor .unified) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor .unified) physical assignment)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor .unified)
      (NativeLookups.selectorsFor .unified) physical (NativePublicSetup.rows initial program .unified)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment assignment) (UnifiedReduced.clockConstraints (p := babyBearModulus) (UnifiedReduced.Setup.tableRV (p := babyBearModulus) initial)) := by
  apply NativeBridge.constraints_transport (UnifiedReduced.clockConstraints (p := babyBearModulus) (UnifiedReduced.Setup.tableRV (p := babyBearModulus) initial))
    (Airbender.Compiler.CleanArithmeticNative.UnifiedCached.native.environment physical (Verification.environment assignment).data)
    (Verification.environment assignment) 137
    (NativeBridge.ScopeChecks.unified_scope (UnifiedReduced.Setup.tableRV (p := babyBearModulus) initial))
    (NativeBindings.Unified.environment physical assignment agreement) rfl
  exact NativeClock.Unified.physical initial program bound physical _ accepted arguments

end Airbender.Compiler.NativeClock.Unified
