module
public import Proven.Compiler.WorkerWitnesses.SplitRows
public import Proven.Compiler.WorkerExtension.KeccakColumnParity
public import Proven.Compiler.WorkerExtension.KeccakThetaRho
public import Proven.Compiler.WorkerExtension.KeccakChi5

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler
set_option maxRecDepth 32768

/-- The cached and no-cache worker have the same constraint description. -/
theorem keccakColumnParity_cached_description : KeccakColumnParityCachedDescriptionClaim := by
  unfold KeccakColumnParityCachedDescriptionClaim
  kernel_rfl

/-- Native cached scalar equations and source placements imply every imported equation. -/
theorem keccakColumnParity_cached_arithmetic : KeccakColumnParityCachedArithmeticClaim := WorkerBindings.KeccakColumnParity.arithmetic

/-- A concrete active worker supplies the native arithmetic and placement premises. -/
theorem keccakColumnParity_cached_arithmetic_satisfiable : KeccakColumnParityCachedArithmeticSatisfiableClaim := by
  obtain ⟨physical, accepted, placement⟩ := WorkerExtension.KeccakColumnParity.extension
    (NonVacuous.KeccakSplitSpan.Parity.assignment (p := babyBearModulus) WorkerWitnesses.parityInput)
    WorkerWitnesses.parity_equations
  exact ⟨physical, _, accepted, placement⟩

/-- The cached and no-cache worker have the same constraint description. -/
theorem keccakThetaRho_cached_description : KeccakThetaRhoCachedDescriptionClaim := by
  unfold KeccakThetaRhoCachedDescriptionClaim
  kernel_rfl

/-- Native cached scalar equations and source placements imply every imported equation. -/
theorem keccakThetaRho_cached_arithmetic : KeccakThetaRhoCachedArithmeticClaim := WorkerBindings.KeccakThetaRho.arithmetic

/-- A concrete active worker supplies the native arithmetic and placement premises. -/
theorem keccakThetaRho_cached_arithmetic_satisfiable : KeccakThetaRhoCachedArithmeticSatisfiableClaim := by
  obtain ⟨physical, accepted, placement⟩ := WorkerExtension.KeccakThetaRho.extension
    (NonVacuous.KeccakSplitSpan.ThetaRho.assignment (p := babyBearModulus) WorkerWitnesses.thetaInput)
    WorkerWitnesses.theta_equations
  exact ⟨physical, _, accepted, placement⟩

/-- The cached and no-cache worker have the same constraint description. -/
theorem keccakChi5_cached_description : KeccakChi5CachedDescriptionClaim := by
  unfold KeccakChi5CachedDescriptionClaim
  kernel_rfl

/-- Native cached scalar equations and source placements imply every imported equation. -/
theorem keccakChi5_cached_arithmetic : KeccakChi5CachedArithmeticClaim := WorkerBindings.KeccakChi5.arithmetic

/-- A concrete active worker supplies the native arithmetic and placement premises. -/
theorem keccakChi5_cached_arithmetic_satisfiable : KeccakChi5CachedArithmeticSatisfiableClaim := by
  obtain ⟨physical, accepted, placement⟩ := WorkerExtension.KeccakChi5.extension
    (NonVacuous.KeccakSplitSpan.Chi.assignment (p := babyBearModulus) WorkerWitnesses.chiInput)
    WorkerWitnesses.chi_equations
  exact ⟨physical, _, accepted, placement⟩

end Airbender.Compiler
