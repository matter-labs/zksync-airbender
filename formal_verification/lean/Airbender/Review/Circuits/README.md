# Circuit review

This directory describes the imported circuit families as relations between
witnesses and observable inputs/outputs. Each family identifies its actual
constraint artifact, the words or state effects represented by its columns, and
the Sail or project reference against which those effects are checked. Local row
claims and complete instruction or worker execution have distinct scopes.

## Checked results

The six ordinary-family local claims prove their mapped register/memory and PC
effects agree with original Sail, under public initialization/configuration/table
conditions and logical matching/membership. Their public-image initialization
seeds ROM shadows with public values and excludes native ROM-load traces with
zero shadows. The pooled ROM-view execution path supplies the separate native
transport. These local histories derive reads, operand
bounds and preprocessing. A standalone local G claim retains explicit operand
bounds; its integrated worker connection derives them from initialized history.

Bigint's local public claim derives native addresses; its seven operation effects
are connected in [worker execution](../Trace/Workers/Bigint/README.md#checked-results).
Extended-BLAKE and Keccak local phase contracts feed their
[complete worker results](../Trace/Workers/README.md#checked-results).
The [unified results](../Trace/UnifiedReduced/README.md#checked-results) cover
additional standard/custom execution and selected caller windows.

These are arbitrary-witness soundness implications for the stated relations,
not completeness, Rust-generation correspondence or every global padding/ABI boundary.

Each family owns its local references, imported artifact selection and named
observable mappings. Start with [Properties](../Helpers/Properties.lean),
then select a family below.

| Family | Review entry | Main distinction |
| --- | --- | --- |
| ADD/SUB | [Guide](AddSub/README.md) | Standard row effects versus custom arithmetic and callers. |
| Jump/branch/SLT | [Guide](JumpBranchSlt/README.md) | Configuration and the explicit external canonical terminal-PC boundary. |
| MUL/DIV | [Guide](MulDiv/README.md) | Four admitted operations, including zero divisors. |
| Shift/binop | [Guide](ShiftBinop/README.md) | Register/immediate preprocessing and original REV8 decoding. |
| Word memory | [Guide](WordMemory/README.md) | Physical RAM/ROM behavior and the discarded-LW profile. |
| Subword memory | [Guide](SubwordMemory/README.md) | Aligned-cell mapping, merged stores and public ROM bytes. |
| Unified reduced | [Guide](UnifiedReduced/README.md) | Local selector slices versus mixed execution and callers. |
| Bigint | [Guide](Bigint/README.md) | Address/operation effects versus full caller-control ABI. |
| BLAKE2 G | [Guide](Blake2G/README.md) | A local G operation versus a complete work-vector span. |
| Extended BLAKE | [Guide](Blake2Round/README.md) | Worker phases versus complete seven-/ten-round compression. |
| Keccak | [Guide](Keccak/README.md) | Per-mode effects versus a complete permutation span. |
| Initialization/teardown | [Guide](Initialization/README.md) | Actual standalone/inline GKR products and computed boundary tokens. |

For a model, inspect its imported constraints, represented inputs/outputs and
interface assumptions. Follow the named columns to the artifact and the selected
reference to its actual semantics. Preserve the theorem's field minimum and
serialized inverse conditions; generic field proofs do not establish a Proth120 import.

Shared [context](../Helpers/Context/README.md), [decoder](../Helpers/Decoder/README.md)
and [memory](../Helpers/Memory/README.md) supply initialized-history interpretation.
Imported columns live in Data; Review Tables define their logical interpretation; Rust setup correspondence
remains unproved. [Whole execution](../Trace/README.md) is a separate route.

Jump/branch/SLT, MUL/DIV and shift/binop theorem implementations retain the
documented pooled proof-assembly dependency. Their local statements and models
do not acquire a whole-run assumption.
