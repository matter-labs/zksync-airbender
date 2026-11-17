# Import: from circuit JSON to the definitions the claims use

The claims use definitions imported from Airbender's circuit JSON (`importedConstraints`, its timestamp queries,
memory ports, decoder and clock columns, inits/teardowns layouts). This directory says what those JSON files mean
and how they get into Lean. The parser, decoder and placement claims fix the meaning
of the executable import procedures.

## What to read

| File | Role |
| --- | --- |
| [Transcribe.lean](Transcribe.lean), [TranscribeCommand.lean](TranscribeCommand.lean) | **Trusted** (`TRUSTED: review`): the import_circuit command turns a JSON file into `importedCircuit : Circuit` (and its text `importedCircuitSourceBytes`): the file read, `Json.parse` then `Circuit.decode` (both fixed by claims), reflection as a kernel term. The shared form of the 14 cached captures emits no text and replaces large arrays of the reflected circuit with shared constants. Not kernel-checked, except for the inits/teardowns files: the kernel parses and decodes the no-cache file in the plain form (`StandaloneBytesClaim`) and the cached file in the shared form (`SharedBytesClaim`). |
| [NativeRamProducts.lean](NativeRamProducts.lean) | Transcribe the native initialization product graphs. The kernel checks their extraction from the existing typed circuit artifacts. |
| [NativeGrid.lean](NativeGrid.lean) | **Trusted** (`TRUSTED: review`): the compiled comparison of the subword and unified fixed rows with the native JSON rows (test library only). |
| [SetupEmit.lean](SetupEmit.lean) | **Trusted** (`TRUSTED: review`): the setup JSON reader `parseSetup` (`Json.parse`, then read field by field) and the emission of the JSON blocks as kernel data. The `with grids` form (no setup import uses it) also replaces each table region by a grid block after a compiled row-by-row comparison with the JSON (`checkColumn`). |
| [JsonGrammar.lean](JsonGrammar.lean), [Theorems.lean](Theorems.lean) | The byte-level JSON grammar (RFC 8259, integers only) and the claims of the parser and the decoder: `ParseSoundClaim` (it accepts only grammatical texts without duplicate member names, and returns their value), `TextUniqueClaim` (a text has one value) and `DecodeClaim` (the decoder returns exactly the circuit whose serde JSON is the value). Each claim has its own separate witness statement. |
| [Schema.lean](Schema.lean), [Json.lean](Json.lean), [Serde.lean](Serde.lean) | The serde mirror: the Lean types of the artifact and, next to each, `Serde.encode`, the JSON serde writes for it. |
| [BabyBear.lean](BabyBear.lean), [Coefficients.lean](Coefficients.lean) | Montgomery coefficients and their signed representatives (`ConstantsClaim` in [Theorems.lean](Theorems.lean)). |
| [Columns.lean](Columns.lean), [Operations.lean](Operations.lean), [InitsTeardownsLayout.lean](InitsTeardownsLayout.lean) | **The meaning**: pure functions from a `Circuit` to operations and column descriptors. `PlacementsClaim` (in Columns) states the placement index. |
| [SetupBlocks.lean](SetupBlocks.lean) | The meaning of a setup column (`decode`) and of the imported rows (`SetupData.Rows`). Kernel claims make each setup table definition equal to the imported rows: the `SetupImportClaim` and `…ImportClaim` statements next to the definitions ([setup README](../../../artifacts/setup/README.md)). `test/Tests/ImportSetupSpotChecks.lean` checks single imported values against the JSON. |
| `ArtifactImportClaim` in each `Human/Circuits/<family>/Artifact.lean`; `StandaloneImportClaim`, `UnifiedImportClaim` in `Human/Circuits/InitsTeardowns/` | Every imported definition is the meaning function applied to `importedCircuit`. The kernel evaluates both sides (`proven/Proven/Final/Circuits/*/Artifact.lean`). |

## Spot checks

[ImportSpotChecks.lean](../../../test/Tests/ImportSpotChecks.lean) has kernel examples that a reviewer can repeat
with other values. The comment above each example names the JSON file and the JSON path of its value. For the shared
add-sub (CPU) and chi (worker) imports, the examples read one gate coefficient, one placement entry and one cached
lookup expression. For one add-sub word and one word-memory word, Sail decodes the word, and the decoder table of a
program with that word contains its native query. `SharedBytesClaim`
([InitsTeardowns/SharedArtifact.lean](../Circuits/InitsTeardowns/SharedArtifact.lean)) has the kernel parse and
decode all bytes of the cached inits/teardowns file, which the shared form imports.

`Exec/` holds the executable code: the JSON parser, the decoder, the emitters of the literal terms and FastColumns (copies of
the [Columns](Columns.lean) functions the emitter runs, derived by a command). Each file names the claims that fix its behaviour.
[Trust.lean](../Trust.lean) lists the modules that can use unsafe evaluation or partial procedures.
The [source check](../../../scripts/check_trusted_code.py) enforces that list.
