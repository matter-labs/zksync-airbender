module
public import Proven.Compiler.WorkerWitnesses.Common
public import Proven.Compiler.NativeSatisfiable.Bigint
public import Proven.Compiler.WorkerConstraints.Bigint
public import Proven.Compiler.NativeSatisfiable.BlakeG
public import Proven.Compiler.WorkerConstraints.BlakeG
public import Proven.Compiler.NativeSatisfiable.BlakeRound
public import Proven.Compiler.WorkerConstraints.BlakeRound

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerWitnesses
open NativeArithmetic
set_option maxRecDepth 32768

/-- The accepted Bigint pool row has a full cached worker certificate. -/
noncomputable def bigint : WorkerCertificate :=
  ofExtension .bigint NonVacuous.Bigint.row
    (NativeExtension.Bigint.extension_preserves _ NativeSatisfiable.Bigint.source_satisfied)
    (fun physical placement => WorkerConstraints.Bigint.arguments_of_description physical _ placement
      (Verification.holds_append NonVacuous.Bigint.core NonVacuous.Bigint.clocks))
    (by kernel_rfl)

/-- The certificate retains the selected production worker family. -/
theorem bigint_family : bigint.family = .bigint := rfl

/-- The accepted Blake2G pool row has a full cached worker certificate. -/
noncomputable def blakeG : WorkerCertificate :=
  ofExtension .blakeG NonVacuous.Blake2G.row
    (NativeExtension.BlakeG.extension_preserves _ NativeSatisfiable.BlakeG.source_satisfied)
    (fun physical placement => WorkerConstraints.BlakeG.arguments_of_description physical _ placement
      (Verification.holds_append NonVacuous.Blake2G.core NonVacuous.Blake2G.clocks))
    (by kernel_rfl)

/-- The certificate retains the selected production worker family. -/
theorem blakeG_family : blakeG.family = .blakeG := rfl

/-- The accepted Blake2Round pool row has a full cached worker certificate. -/
noncomputable def blakeRound : WorkerCertificate :=
  ofExtension .blakeRound NonVacuous.Blake2Round.row
    (NativeExtension.BlakeRound.extension_preserves _ NativeSatisfiable.BlakeRound.source_satisfied)
    (fun physical placement => WorkerConstraints.BlakeRound.arguments_of_description physical _ placement
      (Verification.holds_append NonVacuous.Blake2Round.core NonVacuous.Blake2Round.clocks))
    (by kernel_rfl)

/-- The certificate retains the selected production worker family. -/
theorem blakeRound_family : blakeRound.family = .blakeRound := rfl

end Airbender.Compiler.WorkerWitnesses
