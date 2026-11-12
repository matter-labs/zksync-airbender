module
public import Proven.GKRProtocol.CleanLinksNative.WordMemoryCached
public import Proven.Compiler.Lookups.Ranges.WordMemory
public import Proven.Compiler.Lookups.NativeHelpers
public import Proven.Compiler.ScopeChecks
public import Proven.Compiler.Lookups.Vectors.WordMemory

@[expose] public section
namespace Airbender.Compiler.NativeClock.WordMemory
open Airbender Airbender.Compiler Airbender.Trace NativeArithmetic
set_option warningAsError true
set_option maxRecDepth 65536

theorem lookup_inventory (initial : RV.State) (cells : List Cell) : FlatOperation.lookups (WordMemory.clockConstraints (p := babyBearModulus) (ROM.table (p := babyBearModulus) cells (romImageRV initial cells))) =
    Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.rangeExpressions.map Verification.range16 ++ Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryCached.native.genericExpressions.map (fun entry => Lookup.mk (ROM.table (p := babyBearModulus) cells (romImageRV initial cells)).toRaw entry) ++ Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampExpressions.map Trace.timestampLookup := by rfl

/-- Native equations and exact table matching imply every retained CPU clock constraint. -/
theorem physical (initial : RV.State) (program : List RVMachineProgramEntry)
    {actual : ProgramLookupRows} (bound : NativePublicSetup.Bound initial program actual)
    (cells : List Cell) (covers : NativePublicSetup.CoversROM cells)
    (physical : GKRAddress → F) (data : ProverData F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .wordMemory)) physical)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .wordMemory))
      (NativeLookups.selectorsFor (.pooled .wordMemory)) physical (NativePublicSetup.rows initial program (.pooled .wordMemory))) :
    FlatOperation.ConstraintsHoldFlat
      (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data) (WordMemory.clockConstraints (p := babyBearModulus) (ROM.table (p := babyBearModulus) cells (romImageRV initial cells))) := by
  let arithmetic := NativeBindings.WordMemory.scalar_gates physical accepted
  have helpers := NativeHelpers.WordMemory.bounded initial program physical accepted arguments
  apply CleanLinksNative.WordMemoryCached.retained_clock_constraints (ROM.table (p := babyBearModulus) cells (romImageRV initial cells)) physical data arithmetic
  rw [lookup_inventory initial cells]
  exact PredicateChecks.all (PredicateChecks.cons (NativeRangeLookups.WordMemory.range_lookup0 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.WordMemory.range_lookup1 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.WordMemory.range_lookup2 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.WordMemory.generic_lookup0 initial program bound cells covers physical data arithmetic arguments) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestamp_bound0 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestamp_bound1 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestamp_bound2 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestamp_bound3 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestamp_bound4 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestamp_bound5 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestamp_bound6 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.WordMemoryCached.native.timestamp_bound7 physical data arithmetic helpers)) PredicateChecks.nil))))))))))))

/-- Checked placements transfer the complete native row into its logical witness interpretation. -/
theorem logical (initial : RV.State) (program : List RVMachineProgramEntry)
    {actual : ProgramLookupRows} (bound : NativePublicSetup.Bound initial program actual)
    (cells : List Cell) (covers : NativePublicSetup.CoversROM cells)
    (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .wordMemory)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .wordMemory)) physical assignment)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .wordMemory))
      (NativeLookups.selectorsFor (.pooled .wordMemory)) physical (NativePublicSetup.rows initial program (.pooled .wordMemory))) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment assignment) (WordMemory.clockConstraints (p := babyBearModulus) (ROM.table (p := babyBearModulus) cells (romImageRV initial cells))) := by
  apply NativeBridge.constraints_transport (WordMemory.clockConstraints (p := babyBearModulus) (ROM.table (p := babyBearModulus) cells (romImageRV initial cells)))
    (Airbender.Compiler.CleanArithmeticNative.WordMemoryCached.native.environment physical (Verification.environment assignment).data)
    (Verification.environment assignment) 52
    (NativeBridge.ScopeChecks.wordMemory_scope (ROM.table (p := babyBearModulus) cells (romImageRV initial cells)))
    (NativeBindings.WordMemory.environment physical assignment agreement) rfl
  exact NativeClock.WordMemory.physical initial program bound cells covers physical _ accepted arguments

end Airbender.Compiler.NativeClock.WordMemory
