module
public import Proven.GKRProtocol.CleanLinksNative.JumpBranchCached
public import Proven.Compiler.Lookups.Ranges.JumpBranch
public import Proven.Compiler.Lookups.NativeHelpers
public import Proven.Compiler.ScopeChecks
public import Proven.Compiler.Lookups.Vectors.JumpBranch

@[expose] public section
namespace Airbender.Compiler.NativeClock.JumpBranch
open Airbender Airbender.Compiler Airbender.Trace NativeArithmetic
set_option warningAsError true
set_option maxRecDepth 65536

theorem lookup_inventory :
    FlatOperation.lookups (Airbender.JumpBranchSlt.clockConstraints (p := babyBearModulus)) =
    (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.rangeExpressions.map Verification.range16) ++ NativeVectorLookups.JumpBranch.fixedLookups ++
      (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpressions.map Trace.timestampLookup) := by rfl


/-- Native equations and exact table matching imply every retained CPU clock constraint. -/
theorem physical (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → F) (data : ProverData F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .jumpBranchSlt)) physical)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .jumpBranchSlt))
      (NativeLookups.selectorsFor (.pooled .jumpBranchSlt)) physical (NativePublicSetup.rows initial program (.pooled .jumpBranchSlt))) :
    FlatOperation.ConstraintsHoldFlat
      (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) (JumpBranchSlt.clockConstraints (p := babyBearModulus)) := by
  let arithmetic := NativeBindings.JumpBranch.scalar_gates physical accepted
  have helpers := NativeHelpers.JumpBranch.bounded initial program physical accepted arguments
  apply CleanLinksNative.JumpBranchCached.retained_clock_constraints physical data arithmetic
  rw [lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (NativeRangeLookups.JumpBranch.range_lookup0 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.JumpBranch.range_lookup1 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.JumpBranch.range_lookup2 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeRangeLookups.JumpBranch.range_lookup3 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.JumpBranch.generic_lookup0 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.JumpBranch.generic_lookup1 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.JumpBranch.generic_lookup2 initial program physical data arithmetic arguments) (PredicateChecks.cons (NativeVectorLookups.JumpBranch.generic_lookup3 initial program physical data arithmetic arguments) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound0 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound1 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound2 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound3 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound4 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound5 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound6 physical data arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical data) (Airbender.Compiler.CleanArgumentsNative.JumpBranchCached.native.timestamp_bound7 physical data arithmetic helpers)) PredicateChecks.nil))))))))))))))))

/-- Checked placements transfer the complete native row into its logical witness interpretation. -/
theorem logical (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → F) (assignment : Nat → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .jumpBranchSlt)) physical)
    (agreement : PlacementAgreement (NativeLookups.circuitFor (.pooled .jumpBranchSlt)) physical assignment)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .jumpBranchSlt))
      (NativeLookups.selectorsFor (.pooled .jumpBranchSlt)) physical (NativePublicSetup.rows initial program (.pooled .jumpBranchSlt))) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment assignment) (JumpBranchSlt.clockConstraints (p := babyBearModulus)) := by
  apply NativeBridge.constraints_transport (JumpBranchSlt.clockConstraints (p := babyBearModulus))
    (Airbender.Compiler.CleanArithmeticNative.JumpBranchCached.native.environment physical (Verification.environment assignment).data)
    (Verification.environment assignment) 55
    (NativeBridge.ScopeChecks.jumpBranch_scope)
    (NativeBindings.JumpBranch.environment physical assignment agreement) rfl
  exact NativeClock.JumpBranch.physical initial program physical _ accepted arguments

end Airbender.Compiler.NativeClock.JumpBranch
