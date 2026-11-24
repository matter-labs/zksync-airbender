module
public import Human.Compiler.WorkerCertificates
public import Proven.KernelRfl
public import Proven.Constraints

@[expose] public section
namespace Airbender.Compiler.WorkerConstraints
open NativeArithmetic NativeWorkerLookups
set_option warningAsError true

/-- Every worker description includes its equations and all native timestamp queries. -/
noncomputable def constraints : Family → List (FlatOperation F)
  | .bigint => Bigint.clockConstraints Bigint.setupTable
  | .blakeG => Blake2G.clockConstraints (Blake2G.setupTable Blake2G.Control.controllerRows)
  | .blakeRound => Blake2Round.clockConstraints Blake2Round.setupTable
  | .columnParity => Keccak.Split.ColumnParity.clockConstraints Keccak.Split.ColumnParity.setup
  | .thetaRho => Keccak.Split.ThetaRho.clockConstraints Keccak.Split.ThetaRho.setup
  | .chi5 => Keccak.Split.Chi5.clockConstraints Keccak.Split.Chi5.setup

/-- The cached structured statements are exactly the description assertions. -/
theorem assertion_binding (family : Family) :
    FlatOperation.constraints (constraints family) =
      FlatOperation.constraints (Circuit.equations (circuitFor family)) := by
  cases family <;> kernel_rfl

/-- Native assertion preservation and complete lookup membership give the full description. -/
theorem holds_of_lookups (family : Family) (logical : Nat → F)
    (assertions : FlatOperation.ConstraintsHoldFlat (Verification.environment logical)
      (Circuit.equations (circuitFor family)))
    (lookups : ∀ query ∈ FlatOperation.lookups (constraints family),
      query.Contains (Verification.environment logical)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints family) := by
  apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
  refine ⟨?_, lookups⟩
  intro expression member
  rw [assertion_binding] at member
  exact (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp assertions).1 expression member

end Airbender.Compiler.WorkerConstraints
