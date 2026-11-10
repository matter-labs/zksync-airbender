import Airbender.Proofs.GKRProtocol.WorkerPortChecks.BlakeGCached.Typed
import Airbender.Import.GKRProtocol.NumericWorkerPortImport

namespace Airbender.Compiler.WorkerPortChecks.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_worker_port_capture columns0 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 0).take 16, []⟩)

numeric_worker_port_capture columns16 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 16).take 16, []⟩)

numeric_worker_port_capture columns32 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 32).take 16, []⟩)

numeric_worker_port_capture columns48 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 48).take 16, []⟩)

numeric_worker_port_capture columns64 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 64).take 16, []⟩)

numeric_worker_port_capture columns80 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 80).take 16, []⟩)

numeric_worker_port_capture columns96 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 96).take 15, []⟩)

numeric_worker_port_capture bounds0 := NumericWorkerPortChecks.encode (⟨[], (original.bounds.drop 0).take 18⟩)

noncomputable def data : NumericWorkerPortChecks.Data :=
  ⟨((columns0.columns ++ (columns16.columns ++ columns32.columns)) ++ ((columns48.columns ++ columns64.columns) ++ (columns80.columns ++ columns96.columns))), bounds0.bounds⟩

end Airbender.Compiler.WorkerPortChecks.BlakeGCached
