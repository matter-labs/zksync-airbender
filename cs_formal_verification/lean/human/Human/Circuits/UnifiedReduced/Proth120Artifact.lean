module
public import Human.Import.Exec.Proth120Rows

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120

set_option maxRecDepth 8192 in
import_proth120_rows importedConstraints importedLayout from
  "../../cs/compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json"

/-- The emitted Clean row and window/port descriptors are the interpretations of the four
    source JSON sections and their placement, memory and inline gate metadata. -/
def ArtifactImportClaim : Prop :=
  (∀ (setup : Table (ZMod proth120Modulus) (fields 10)),
    importedConstraintsSource.operations importedConstraintsLayoutSource setup =
      .ok (importedConstraints setup, importedConstraintsTimestampLookups)) ∧
  Circuit.initsTeardownsLayout importedConstraintsLayoutSource false = .ok importedLayout ∧
  Circuit.traceColumns importedConstraintsLayoutSource = .ok importedConstraintsTraceColumns ∧
  Circuit.memoryPorts importedConstraintsLayoutSource = .ok importedConstraintsMemoryPorts ∧
  Circuit.decoderColumns importedConstraintsLayoutSource = .ok importedConstraintsDecoderColumns

end Airbender.UnifiedReduced.Proth120
