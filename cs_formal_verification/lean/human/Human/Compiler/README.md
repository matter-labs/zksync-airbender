# Cached compiler captures

[Capture.lean](Capture.lean) gives the typed source snapshot and complete compiled artifact.
The [ADD/SUB capture](Captures/AddSub.lean) and ten other capture modules read native exports for cached compilation.
[Theorems.lean](Theorems.lean) states that each capture has the existing circuit's constraint description.
Only the compiled layers differ. Each capture also has a cached arithmetic preservation claim.
The proof binds every scalar cache, native sparse gate and logical placement to the checked arithmetic model.
[NativeTargets.lean](NativeTargets.lean) gives three whole-machine corollaries.
[NativeMachineArguments.lean](NativeMachineArguments.lean) supplies cached physical equations,
checked placements and exact natural lookup matching. These derive all CPU clock constraints
and public decoder membership. Worker constraints, participation, state matching, request
matching and shared memory matching remain explicit interfaces.

[NativePublicSetup.lean](NativePublicSetup.lean) binds public setup rows to fixed regions,
public ROM bytes and native program projections. Capacity, nonzero selector masks and omitted
zero coordinates are explicit public setup properties. The fixed and fixture-ROM regions
have complete compiled comparisons under [NativeFixedRows/Bindings.lean](NativeFixedRows/Bindings.lean).
These comparisons are trusted compiled code. They do not prove a general Rust setup generator
correct for every possible program or ROM image.

The [import command](../Import/CompilerCapture.lean) performs trusted transcription. Its native JSON conversion uses the current schema.
It checks scalar bounds and fixed array lengths. It orders map entries as Rust BTree maps.
It does not import proof code. The ordinary circuit decoder stays unchanged.
The kernel checks the emitted terms. The file read and JSON conversion are trusted.

The [drift check](../../../scripts/check_compiler_captures.py) checks every input's SHA-256, rejects duplicate JSON keys and compares each full
compiled artifact with the production cached JSON. It also checks the complete source sidecar.
CI regenerates all eleven source/compiler pairs and compares their bytes.
The source counts retain lookup, range, memory and executor interfaces. Arithmetic preservation alone does not cover them.

The native lookup selectors cover every primitive query once. Each cache or copy expansion follows actual compiled definitions.
[NativeLookups.lean](NativeLookups.lean) states the expanded tuple interface.
[LookupArgument.lean](LookupArgument.lean) states exact matching with public setup rows and natural multiplicities.
A sampled rational equation does not supply this matching. The kernel binds these tuples to the checked native leaf encodings.

The proof wrappers use the kernel_exact tactic when elaborator conversion repeats a large artifact reduction.
The enclosing theorem receives the complete kernel type check. A regression rejects a proof with the wrong type.
