# Cached compiler captures

[Capture.lean](Capture.lean) gives the typed source snapshot and complete compiled artifact.
The [ADD/SUB capture](Captures/AddSub.lean) and ten other capture modules read native exports for cached compilation.
[Theorems.lean](Theorems.lean) states that each capture has the existing circuit's constraint description.
Only the compiled layers differ. Arithmetic preservation is a separate obligation.

The [import command](../Import/CompilerCapture.lean) performs trusted transcription. Its native JSON conversion uses the current schema.
It checks scalar bounds and fixed array lengths. It orders map entries as Rust BTree maps.
It does not import proof code. The ordinary circuit decoder stays unchanged.
The kernel checks the emitted terms. The file read and JSON conversion are trusted.

The [drift check](../../../scripts/check_compiler_captures.py) checks every input's SHA-256, rejects duplicate JSON keys and compares each full
compiled artifact with the production cached JSON. It also checks the complete source sidecar.
CI regenerates all eleven source/compiler pairs and compares their bytes.
The source counts retain lookup, range, memory and executor interfaces. Arithmetic preservation alone does not cover them.
