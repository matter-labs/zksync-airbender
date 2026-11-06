import Airbender.Proofs.ReducedMachine.ArtifactChecks
import Airbender.Review.Circuits.ShiftBinop.Artifact

set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- error: native reduced-machine lookups require their explicit target -/
#guard_msgs in
import_clean refusedReduced from "../../cs/reduced_machine_preprocessed_layout.json" trace_metadata

/-- error: native reduced-machine lookups require their explicit target -/
#guard_msgs in
import_clean refusedReducedWord from "../../cs/reduced_machine_preprocessed_layout.json" word_memory_lookups trace_metadata

/-- error: native reduced-machine lookups require their explicit target -/
#guard_msgs in
import_clean refusedStandalone from "../../cs/add_sub_lui_auipc_mop_preprocessed_layout.json" reduced_machine_lookups

/-- error: choose one native fixed-table profile -/
#guard_msgs in
import_clean crossedReduced from "../../cs/reduced_machine_preprocessed_layout.json" word_memory_lookups reduced_machine_lookups

namespace Tests.ReducedMachineEmission
open Airbender

example {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4)) :
    (ReducedMachine.importedConstraints setup).length = 141 := by rfl

example : ReducedMachine.importedConstraintsTraceColumns.execute = 4 := by rfl
example : ReducedMachine.importedConstraintsDecoderColumns.rdIsZero = 8 := by rfl
example : ReducedMachine.importedConstraintsMemoryPorts.size = 3 := by rfl
example : ReducedMachine.importedConstraintsSetupColumns.traceLength = 8388608 := by rfl

example : ReducedMachine.importedConstraintsRequestColumns = ⟨91,93,some 92,3⟩ := rfl
example : ShiftBinop.importedConstraintsRequestColumns = ⟨37,38,none,3⟩ := rfl

end Tests.ReducedMachineEmission
