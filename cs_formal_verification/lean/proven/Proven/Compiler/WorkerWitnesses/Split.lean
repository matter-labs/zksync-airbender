module
public import Proven.Compiler.WorkerWitnesses.Common
public import Proven.Compiler.WorkerWitnesses.SplitRows
public import Proven.Compiler.WorkerExtension.KeccakColumnParity
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity
public import Proven.Compiler.WorkerExtension.KeccakThetaRho
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho
public import Proven.Compiler.WorkerExtension.KeccakChi5
public import Proven.Compiler.WorkerConstraints.KeccakChi5

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerWitnesses
open NativeArithmetic
set_option maxRecDepth 32768

/-- The accepted split-worker row has a full cached worker certificate. -/
noncomputable def columnParity : WorkerCertificate :=
  ofExtension .columnParity (NonVacuous.KeccakSplitSpan.Parity.assignment (p := babyBearModulus) parityInput)
    (WorkerExtension.KeccakColumnParity.extension _ parity_equations)
    (fun physical placement => WorkerConstraints.KeccakColumnParity.arguments_of_description physical _ placement parity_holds)
    (by kernel_rfl)

/-- The certificate retains the selected production worker family. -/
theorem columnParity_family : columnParity.family = .columnParity := rfl

/-- The accepted split-worker row has a full cached worker certificate. -/
noncomputable def thetaRho : WorkerCertificate :=
  ofExtension .thetaRho (NonVacuous.KeccakSplitSpan.ThetaRho.assignment (p := babyBearModulus) thetaInput)
    (WorkerExtension.KeccakThetaRho.extension _ theta_equations)
    (fun physical placement => WorkerConstraints.KeccakThetaRho.arguments_of_description physical _ placement theta_holds)
    (by kernel_rfl)

/-- The certificate retains the selected production worker family. -/
theorem thetaRho_family : thetaRho.family = .thetaRho := rfl

/-- The accepted split-worker row has a full cached worker certificate. -/
noncomputable def chi5 : WorkerCertificate :=
  ofExtension .chi5 (NonVacuous.KeccakSplitSpan.Chi.assignment (p := babyBearModulus) chiInput)
    (WorkerExtension.KeccakChi5.extension _ chi_equations)
    (fun physical placement => WorkerConstraints.KeccakChi5.arguments_of_description physical _ placement chi_holds)
    (by kernel_rfl)

/-- The certificate retains the selected production worker family. -/
theorem chi5_family : chi5.family = .chi5 := rfl

end Airbender.Compiler.WorkerWitnesses
