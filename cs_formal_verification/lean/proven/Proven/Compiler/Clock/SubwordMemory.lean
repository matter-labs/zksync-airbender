module
public import Proven.GKRProtocol.CleanLinksNative.SubwordMemoryCached
public import Proven.Compiler.Lookups.Ranges.SubwordMemory
public import Proven.Compiler.Lookups.NativeHelpers
public import Proven.Compiler.ScopeChecks
public import Proven.Compiler.Lookups.Vectors.SubwordMemory

@[expose] public section
namespace Airbender.Compiler.NativeClock.SubwordMemory
open Airbender Airbender.Compiler Airbender.Trace NativeArithmetic
set_option warningAsError true
set_option maxRecDepth 65536

theorem lookup_inventory (initial : RV.State) : FlatOperation.lookups (SubwordMemory.clockConstraints (p := babyBearModulus) (Verification.subwordTable (p := babyBearModulus) (ROM.wordsRV initial))) =
    Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.rangeExpressions.map Verification.range16 ++ Airbender.Compiler.CleanGenericArgumentsNative.SubwordMemoryCached.native.genericExpressions.map (fun entry => Lookup.mk (Verification.subwordTable (p := babyBearModulus) (ROM.wordsRV initial)).toRaw entry) ++ Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampExpressions.map Trace.timestampLookup := by rfl

/-- Native equations and exact table matching imply every retained CPU clock constraint. -/
theorem physical (initial : RV.State) (program : List RVMachineProgramEntry)
    {actual : ProgramLookupRows} (bound : NativePublicSetup.Bound initial program actual)
    (physical : GKRAddress → F) (data : ProverData F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .subwordMemory)) physical)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .subwordMemory))
      (NativeLookups.selectorsFor (.pooled .subwordMemory)) physical (NativePublicSetup.rows initial program (.pooled .subwordMemory))) :
    FlatOperation.ConstraintsHoldFlat
      (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data) (SubwordMemory.clockConstraints (p := babyBearModulus) (Verification.subwordTable (p := babyBearModulus) (ROM.wordsRV initial))) := by
  let arithmetic := NativeBindings.SubwordMemory.scalar_gates physical accepted
  have helpers := NativeHelpers.SubwordMemory.bounded initial program physical accepted arguments
  apply CleanLinksNative.SubwordMemoryCached.retained_clock_constraints (Verification.subwordTable (p := babyBearModulus) (ROM.wordsRV initial)) physical data arithmetic
  rw [lookup_inventory initial]
  exact PredicateChecks.all (PredicateChecks.cons (NativeRangeLookups.SubwordMemory.range_lookup0 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.SubwordMemory.range_lookup1 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.SubwordMemory.range_lookup2 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.SubwordMemory.range_lookup3 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.SubwordMemory.range_lookup4 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.SubwordMemory.generic_lookup0 initial program bound physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.SubwordMemory.generic_lookup1 initial program bound physical data arithmetic arguments) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestamp_bound0 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestamp_bound1 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestamp_bound2 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestamp_bound3 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestamp_bound4 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestamp_bound5 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestamp_bound6 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.SubwordMemoryCached.native.timestamp_bound7 physical data arithmetic helpers)) PredicateChecks.nil)))))))))))))))

/-- Checked placements transfer the complete native row into its logical witness interpretation. -/
theorem logical (initial : RV.State) (program : List RVMachineProgramEntry)
    {actual : ProgramLookupRows} (bound : NativePublicSetup.Bound initial program actual)
    (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .subwordMemory)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .subwordMemory)) physical assignment)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .subwordMemory))
      (NativeLookups.selectorsFor (.pooled .subwordMemory)) physical (NativePublicSetup.rows initial program (.pooled .subwordMemory))) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment assignment) (SubwordMemory.clockConstraints (p := babyBearModulus) (Verification.subwordTable (p := babyBearModulus) (ROM.wordsRV initial))) := by
  apply NativeBridge.constraints_transport (SubwordMemory.clockConstraints (p := babyBearModulus) (Verification.subwordTable (p := babyBearModulus) (ROM.wordsRV initial)))
    (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryCached.native.environment physical (Verification.environment assignment).data)
    (Verification.environment assignment) 68
    (NativeBridge.ScopeChecks.subwordMemory_scope (Verification.subwordTable (p := babyBearModulus) (ROM.wordsRV initial)))
    (NativeBindings.SubwordMemory.environment physical assignment agreement) rfl
  exact NativeClock.SubwordMemory.physical initial program bound physical _ accepted arguments

end Airbender.Compiler.NativeClock.SubwordMemory
