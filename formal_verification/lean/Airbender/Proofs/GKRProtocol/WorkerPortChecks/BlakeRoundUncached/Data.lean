import Airbender.Proofs.GKRProtocol.WorkerPortChecks.BlakeRoundUncached.Typed
import Airbender.Import.GKRProtocol.NumericWorkerPortImport

namespace Airbender.Compiler.WorkerPortChecks.BlakeRoundUncached
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

numeric_worker_port_capture columns176 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 176).take 16, []⟩)

numeric_worker_port_capture columns192 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 192).take 16, []⟩)

numeric_worker_port_capture columns208 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 208).take 16, []⟩)

numeric_worker_port_capture columns224 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 224).take 16, []⟩)

numeric_worker_port_capture columns240 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 240).take 16, []⟩)

numeric_worker_port_capture columns256 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 256).take 16, []⟩)

numeric_worker_port_capture columns272 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 272).take 16, []⟩)

numeric_worker_port_capture columns288 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 288).take 16, []⟩)

numeric_worker_port_capture columns304 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 304).take 16, []⟩)

numeric_worker_port_capture columns320 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 320).take 16, []⟩)

numeric_worker_port_capture columns336 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 336).take 16, []⟩)

numeric_worker_port_capture columns352 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 352).take 16, []⟩)

numeric_worker_port_capture columns368 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 368).take 16, []⟩)

numeric_worker_port_capture columns384 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 384).take 16, []⟩)

numeric_worker_port_capture columns400 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 400).take 16, []⟩)

numeric_worker_port_capture columns416 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 416).take 16, []⟩)

numeric_worker_port_capture columns432 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 432).take 16, []⟩)

numeric_worker_port_capture columns448 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 448).take 16, []⟩)

numeric_worker_port_capture columns464 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 464).take 16, []⟩)

numeric_worker_port_capture columns480 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 480).take 16, []⟩)

numeric_worker_port_capture columns496 := NumericWorkerPortChecks.encode (⟨(original.columns.drop 496).take 11, []⟩)

numeric_worker_port_capture bounds0 := NumericWorkerPortChecks.encode (⟨[], (original.bounds.drop 0).take 32⟩)

numeric_worker_port_capture bounds32 := NumericWorkerPortChecks.encode (⟨[], (original.bounds.drop 32).take 32⟩)

numeric_worker_port_capture bounds64 := NumericWorkerPortChecks.encode (⟨[], (original.bounds.drop 64).take 22⟩)

noncomputable def data : NumericWorkerPortChecks.Data :=
  ⟨(((((columns0.columns ++ columns16.columns) ++ (columns32.columns ++ columns48.columns)) ++ ((columns64.columns ++ columns80.columns) ++ (columns96.columns ++ columns112.columns))) ++ (((columns128.columns ++ columns144.columns) ++ (columns160.columns ++ columns176.columns)) ++ ((columns192.columns ++ columns208.columns) ++ (columns224.columns ++ columns240.columns)))) ++ ((((columns256.columns ++ columns272.columns) ++ (columns288.columns ++ columns304.columns)) ++ ((columns320.columns ++ columns336.columns) ++ (columns352.columns ++ columns368.columns))) ++ (((columns384.columns ++ columns400.columns) ++ (columns416.columns ++ columns432.columns)) ++ ((columns448.columns ++ columns464.columns) ++ (columns480.columns ++ columns496.columns))))), (bounds0.bounds ++ (bounds32.bounds ++ bounds64.bounds))⟩

end Airbender.Compiler.WorkerPortChecks.BlakeRoundUncached
