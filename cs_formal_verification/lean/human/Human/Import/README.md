# Import: from circuit JSON to the definitions the claims use

The claims use definitions imported from Airbender's circuit JSON (`importedConstraints`, its timestamp queries,
memory ports, decoder and clock columns, inits/teardowns layouts). This directory says what those JSON files mean
and how they get into Lean. The parser, decoder and placement claims fix the meaning
of the executable import procedures.

## What to read

| File | Role |
| --- | --- |
| [Transcribe.lean](Transcribe.lean), [TranscribeCommand.lean](TranscribeCommand.lean) | **Trusted** (`TRUSTED: review`): the import_circuit command turns a JSON file into `importedCircuit : Circuit` (and its text `importedCircuitSourceBytes`): the file read, `Json.parse` then `Circuit.decode` (both fixed by claims), reflection as a kernel term. The shared form of the 14 cached captures emits no text and replaces large arrays of the reflected circuit with shared constants. Not kernel-checked, except for the standalone inits/teardowns artifact, whose bytes the kernel parses and decodes in the plain and in the shared form (`StandaloneBytesClaim`, `SharedBytesClaim`). |
| [NativeRamProducts.lean](NativeRamProducts.lean) | Transcribe the native initialization product graphs. The kernel checks their extraction from the existing typed circuit artifacts. |
| [NativeGrid.lean](NativeGrid.lean) | **Trusted** (`TRUSTED: review`): compiled comparisons of native JSON rows with mathematical row functions. This is the DECISION B setup binding. Input validation retains small content stamps. |
| [SetupEmit.lean](SetupEmit.lean) | **Trusted** (`TRUSTED: review`): setup-table JSON to compressed column blocks (`Json.parse`, then read field by field), including the row-by-row comparison of grid blocks with the JSON. |
| [JsonGrammar.lean](JsonGrammar.lean), [Theorems.lean](Theorems.lean) | The byte-level JSON grammar (RFC 8259, integers only) and the claims of the parser and the decoder: `ParseSoundClaim` (it accepts only grammatical texts without duplicate member names, and returns their value), `TextUniqueClaim` (a text has one value) and `DecodeClaim` (the decoder returns exactly the circuit whose serde JSON is the value). Each claim has its own separate witness statement. |
| [Schema.lean](Schema.lean), [Json.lean](Json.lean), [Serde.lean](Serde.lean) | The serde mirror: the Lean types of the artifact and, next to each, `Serde.encode`, the JSON serde writes for it. |
| [BabyBear.lean](BabyBear.lean), [Coefficients.lean](Coefficients.lean) | Montgomery coefficients and their signed representatives (`ConstantsClaim` in [Theorems.lean](Theorems.lean)). |
| [Columns.lean](Columns.lean), [Operations.lean](Operations.lean), [InitsTeardownsLayout.lean](InitsTeardownsLayout.lean) | **The meaning**: pure functions from a `Circuit` to operations and column descriptors. `PlacementsClaim` (in Columns) states the placement index. |
| [SetupBlocks.lean](SetupBlocks.lean) | The meaning of a setup column (`decode`). |
| `ArtifactImportClaim` in each `Human/Circuits/<family>/Artifact.lean`; `StandaloneImportClaim`, `UnifiedImportClaim` in `Human/Circuits/InitsTeardowns/` | Every imported definition is the meaning function applied to `importedCircuit`. The kernel evaluates both sides (`proven/Proven/Final/Circuits/*/Artifact.lean`). |

## Spot checks

[ImportSpotChecks.lean](../../../test/Tests/ImportSpotChecks.lean) has kernel examples that a reviewer can repeat
with other values. The comment above each example names the JSON file and the JSON path of its value. For the shared
add-sub (CPU) and chi (worker) imports, the examples read one gate coefficient, one placement entry and one cached
lookup expression. For one add-sub word and one word-memory word, Sail decodes the word, and the decoder table of a
program with that word contains its native query. `SharedBytesClaim`
([InitsTeardowns/SharedArtifact.lean](../Circuits/InitsTeardowns/SharedArtifact.lean)) has the kernel parse and
decode all bytes of a file that the shared form imports.

`Exec/` holds the executable code: the JSON parser, the decoder, the emitters of the literal terms and FastColumns (copies of
the [Columns](Columns.lean) functions the emitter runs, derived by a command). Each file names the claims that fix its behaviour.
[Trust.lean](../Trust.lean) lists the modules that can use unsafe evaluation or partial procedures.
The [source check](../../../scripts/check_trusted_code.py) enforces that list.
