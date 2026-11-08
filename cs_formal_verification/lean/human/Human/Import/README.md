# Import: from circuit JSON to the definitions the claims use

The claims use definitions imported from Airbender's circuit JSON (`importedConstraints`, its timestamp queries,
memory ports, decoder and clock columns, inits/teardowns layouts). This directory says what those JSON files mean
and how they get into Lean. The JSON parser and the emitters need no review: claims fix what they do.

## What to read

| File | Role |
| --- | --- |
| [Transcribe.lean](Transcribe.lean), [TranscribeCommand.lean](TranscribeCommand.lean) | **Trusted** (headed `TRUSTED: review`): a JSON file becomes `importedCircuit : Circuit` and its text `importedCircuitSourceBytes`. Not kernel-checked. |
| [SetupEmit.lean](SetupEmit.lean) | **Trusted**: setup-table JSON to compressed column blocks, including the row-by-row comparison of grid blocks with the JSON. |
| [Schema.lean](Schema.lean), [Json.lean](Json.lean) | The serde mirror: the Lean types of the artifact, decoded by derived `FromJson` instances. |
| [BabyBear.lean](BabyBear.lean), [Coefficients.lean](Coefficients.lean) | Montgomery coefficients and their signed representatives (proved). |
| [Columns.lean](Columns.lean), [Operations.lean](Operations.lean), [InitsTeardownsLayout.lean](InitsTeardownsLayout.lean) | **The meaning**: pure functions from a `Circuit` to operations and column descriptors. |
| [SetupBlocks.lean](SetupBlocks.lean) | The meaning of a setup column (`decode`). |
| `ArtifactImportClaim` in each `Human/Circuits/<family>/Artifact.lean`; `StandaloneImportClaim`, `UnifiedImportClaim` in `Human/Circuits/InitsTeardowns/` | The imported definitions are the meaning functions applied to `importedCircuit` (kernel-checked: `slop/Slop/Final/Circuits/*/Artifact.lean`). |

`Exec/` holds the executable code (the emitters); each file names the claims that fix its behaviour.
