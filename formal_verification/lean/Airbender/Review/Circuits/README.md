# Circuit review

This directory describes the imported circuit families as relations between
witnesses and observable inputs/outputs. Each family identifies its actual
constraint artifact, the words or state effects represented by its columns, and
the Sail or project reference against which those effects are checked. Local row
claims and complete instruction or worker execution have distinct scopes.

Each family owns its local references, imported artifact selection and named
observable mappings. Start with [Properties](../Helpers/Properties.lean),
then select a family below.

| Family | Review entry | Main distinction |
| --- | --- | --- |
| ADD/SUB | [Guide](AddSub/README.md) | Standard row effects versus custom arithmetic and callers. |
| Jump/branch/SLT | [Guide](JumpBranchSlt/README.md) | Configuration and unresolved terminal-PC normalization. |
| MUL/DIV | [Guide](MulDiv/README.md) | Four admitted operations, including zero divisors. |
| Shift/binop | [Guide](ShiftBinop/README.md) | Register/immediate preprocessing and original REV8 decoding. |
| Word memory | [Guide](WordMemory/README.md) | Physical RAM/ROM behavior and the discarded-LW profile. |
| Subword memory | [Guide](SubwordMemory/README.md) | Aligned-cell mapping, merged stores and public ROM bytes. |
| Unified reduced | [Guide](UnifiedReduced/README.md) | Local selector slices versus mixed execution and callers. |
| Bigint | [Guide](Bigint/README.md) | Address/operation effects versus full caller-control ABI. |
| BLAKE2 G | [Guide](Blake2G/README.md) | A local G operation versus a complete work-vector span. |
| Extended BLAKE | [Guide](Blake2Round/README.md) | Worker phases versus complete seven-/ten-round compression. |
| Keccak | [Guide](Keccak/README.md) | Per-mode effects versus a complete permutation span. |

For a model, inspect its imported constraints, represented inputs/outputs and
interface assumptions. Follow the named columns to the artifact and the selected
reference to its actual semantics. Preserve the theorem's field minimum and
serialized inverse conditions; generic field proofs do not establish a Proth120 import.

Shared [context](../Helpers/Context/README.md), [decoder](../Helpers/Decoder/README.md)
and [memory](../Helpers/Memory/README.md) supply initialized-history interpretation.
Circuit Tables directories contain modeled setup rows; Rust setup correspondence
remains unproved. [Whole execution](../Trace/README.md) is a separate route.

Jump/branch/SLT, MUL/DIV and shift/binop theorem implementations retain the
documented pooled proof-assembly dependency. Their local statements and models
do not acquire a whole-run assumption.
