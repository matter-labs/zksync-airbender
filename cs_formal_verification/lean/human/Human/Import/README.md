# Import: from circuit JSON to the definitions the claims use

The claims use definitions imported from Airbender's circuit JSON (`importedConstraints`, its timestamp queries,
memory ports, decoder and clock columns, inits/teardowns layouts). This directory says what those JSON files mean
and how they get into Lean. As for the RV32 spec and its Sail equivalence, claims fix what the executable code does,
so the code itself needs no review.

## What to read

| File | Role |
| --- | --- |
| [Transcribe.lean](Transcribe.lean), [TranscribeCommand.lean](TranscribeCommand.lean) | **Trusted** (`TRUSTED: review`): the import_circuit command turns a JSON file into `importedCircuit : Circuit` (and its text `importedCircuitSourceBytes`): `Json.parse`, the `FromJson` instances derived for the schema, reflection as a kernel term. Not kernel-checked. |
| [SetupEmit.lean](SetupEmit.lean) | **Trusted** (`TRUSTED: review`): setup-table JSON to compressed column blocks, including the row-by-row comparison of grid blocks with the JSON. |
| [JsonGrammar.lean](JsonGrammar.lean), [Theorems.lean](Theorems.lean) | The byte-level JSON grammar (RFC 8259, integers only) and the parser's claims: `ParseSoundClaim` (it accepts only grammatical texts without duplicate member names, and returns their value) and `TextUniqueClaim` (a text has one value). |
| [Schema.lean](Schema.lean), [Json.lean](Json.lean) | The serde mirror: the Lean types of the artifact. |
| [BabyBear.lean](BabyBear.lean), [Coefficients.lean](Coefficients.lean) | Montgomery coefficients and their signed representatives (proved). |
| [Columns.lean](Columns.lean), [Operations.lean](Operations.lean), [InitsTeardownsLayout.lean](InitsTeardownsLayout.lean) | **The meaning**: pure functions from a `Circuit` to operations and column descriptors. `PlacementsClaim` (in Columns) states the placement index. |
| [SetupBlocks.lean](SetupBlocks.lean) | The meaning of a setup column (`decode`). |
| `ArtifactImportClaim` in each `Human/Circuits/<family>/Artifact.lean`; `StandaloneImportClaim`, `UnifiedImportClaim` in `Human/Circuits/InitsTeardowns/` | Every imported definition is the meaning function applied to `importedCircuit`. The kernel evaluates both sides (`slop/Slop/Final/Circuits/*/Artifact.lean`). |

`Exec/` holds the executable code: the JSON parser and the emitters of the literal terms. No need to review it:
each file names the claims that fix its behaviour.
