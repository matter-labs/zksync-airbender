module
public import Proven.NonVacuous.DynamicCopyLoop.NativeSource
public import Proven.Compiler.WorkerWitnesses.Common
public import Proven.Compiler.WorkerConstraints.Bigint

@[expose] public section
namespace Airbender.NonVacuous.DynamicCopyLoop
open Airbender.Compiler NativeArithmetic
set_option warningAsError true

/-- Each submitted COPY worker has native cached gates, source placement and public lookup matching. -/
noncomputable def workerCertificate (index : Fin 2) : WorkerCertificate :=
  WorkerWitnesses.ofExtension .bigint (workerAssignment index)
    (NativeExtension.Bigint.extension_preserves _ (worker_source_satisfied index))
    (fun physical placement => WorkerConstraints.Bigint.arguments_of_description physical _ placement
      (worker_satisfies index))
    (by fin_cases index <;> kernel_rfl)

/-- The cached worker certificates describe exactly the two submitted bigint rows. -/
theorem worker_rows_certified : WorkerRowsCertified workers := by
  refine ⟨(List.finRange 2).map workerCertificate, ?_, rfl⟩
  rfl

end Airbender.NonVacuous.DynamicCopyLoop
