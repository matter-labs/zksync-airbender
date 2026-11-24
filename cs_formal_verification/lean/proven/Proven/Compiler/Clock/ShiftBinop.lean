module
public import Proven.GKRProtocol.CleanLinksNative.ShiftBinopCached
public import Proven.Compiler.Lookups.Ranges.ShiftBinop
public import Proven.Compiler.Lookups.NativeHelpers
public import Proven.Compiler.ScopeChecks
public import Proven.Compiler.Lookups.Vectors.ShiftBinop

@[expose] public section
namespace Airbender.Compiler.NativeClock.ShiftBinop
open Airbender Airbender.Compiler Airbender.Trace NativeArithmetic
set_option warningAsError true
set_option maxRecDepth 65536

theorem lookup_inventory : FlatOperation.lookups (ShiftBinop.clockConstraints (p := babyBearModulus)) =
    Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.rangeExpressions.map Verification.range16 ++ Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.genericExpressions.map (fun entry => Lookup.mk (Verification.shiftBinopTable (p := babyBearModulus)).toRaw entry) ++ Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampExpressions.map Trace.timestampLookup := by rfl

/-- Native equations and exact table matching imply every retained CPU clock constraint. -/
theorem physical (initial : RV.State) (program : List RVMachineProgramEntry)
    {actual : ProgramLookupRows} (bound : NativePublicSetup.Bound initial program actual)
    (physical : GKRAddress → F) (data : ProverData F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .shiftBinop)) physical)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .shiftBinop))
      (NativeLookups.selectorsFor (.pooled .shiftBinop)) physical (NativePublicSetup.rows initial program (.pooled .shiftBinop))) :
    FlatOperation.ConstraintsHoldFlat
      (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical data) (ShiftBinop.clockConstraints (p := babyBearModulus)) := by
  let arithmetic := NativeBindings.ShiftBinop.scalar_gates physical accepted
  have helpers := NativeHelpers.ShiftBinop.bounded initial program physical accepted arguments
  apply CleanLinksNative.ShiftBinopCached.retained_clock_constraints physical data arithmetic
  rw [lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (NativeRangeLookups.ShiftBinop.range_lookup0 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.ShiftBinop.range_lookup1 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.ShiftBinop.generic_lookup0 initial program bound physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.ShiftBinop.generic_lookup1 initial program bound physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.ShiftBinop.generic_lookup2 initial program bound physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.ShiftBinop.generic_lookup3 initial program bound physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.ShiftBinop.generic_lookup4 initial program bound physical data arithmetic arguments) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestamp_bound0 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestamp_bound1 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestamp_bound2 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestamp_bound3 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestamp_bound4 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestamp_bound5 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestamp_bound6 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestamp_bound7 physical data arithmetic helpers)) PredicateChecks.nil)))))))))))))))

/-- Checked placements transfer the complete native row into its logical witness interpretation. -/
theorem logical (initial : RV.State) (program : List RVMachineProgramEntry)
    {actual : ProgramLookupRows} (bound : NativePublicSetup.Bound initial program actual)
    (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .shiftBinop)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .shiftBinop)) physical assignment)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .shiftBinop))
      (NativeLookups.selectorsFor (.pooled .shiftBinop)) physical (NativePublicSetup.rows initial program (.pooled .shiftBinop))) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment assignment) (ShiftBinop.clockConstraints (p := babyBearModulus)) := by
  apply NativeBridge.constraints_transport (ShiftBinop.clockConstraints (p := babyBearModulus))
    (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment physical (Verification.environment assignment).data)
    (Verification.environment assignment) 98
    (NativeBridge.ScopeChecks.shiftBinop_scope)
    (NativeBindings.ShiftBinop.environment physical assignment agreement) rfl
  exact NativeClock.ShiftBinop.physical initial program bound physical _ accepted arguments

end Airbender.Compiler.NativeClock.ShiftBinop
