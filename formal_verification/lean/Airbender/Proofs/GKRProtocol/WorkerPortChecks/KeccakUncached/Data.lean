import Airbender.Proofs.GKRProtocol.WorkerPortChecks.KeccakUncached.Typed
import Airbender.Import.GKRProtocol.NumericWorkerPortImport

namespace Airbender.Compiler.WorkerPortChecks.KeccakUncached
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

numeric_worker_port_capture columns96 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 96).take 16, []⟩)

numeric_worker_port_capture columns112 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 112).take 16, []⟩)

numeric_worker_port_capture columns128 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 128).take 16, []⟩)

numeric_worker_port_capture columns144 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 144).take 16, []⟩)

numeric_worker_port_capture columns160 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 160).take 16, []⟩)

numeric_worker_port_capture columns176 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 176).take 11, []⟩)

numeric_worker_port_capture bounds0 := NumericWorkerPortChecks.encode (⟨[], (original.bounds.drop 0).take 28⟩)

noncomputable def data : NumericWorkerPortChecks.Data :=
  ⟨(((columns0.columns ++ (columns16.columns ++ columns32.columns)) ++ (columns48.columns ++ (columns64.columns ++ columns80.columns))) ++ ((columns96.columns ++ (columns112.columns ++ columns128.columns)) ++ (columns144.columns ++ (columns160.columns ++ columns176.columns)))), bounds0.bounds⟩

end Airbender.Compiler.WorkerPortChecks.KeccakUncached
