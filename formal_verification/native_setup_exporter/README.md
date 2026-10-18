# Native v2 setup table export

This standalone crate calls the pinned dev word-memory table driver, ROM/separator
constructors, decoder preprocessor/materializer and 16-bit scalar table generator.
It exports actual regional rows before physical trace padding, c0 normalization,
LDE and commitments. It does not call the full setup builder or allocate a full
2^24-row setup trace. No witness or GPU work is required.

The public image is explicitly zero-padded by the native loader helper to four
MiB. Text remains a separate input, as in native setup callers. All words use
little-endian encoding. The fixture contains LW x3, SW x3, LW x0 and an explicit
UNIMP word. Unsupported decoder slots retain the native all-minus-one sentinel.
The artifact preserves every generic tuple, native table ID/offset, decoder slot,
range16 value and public image/text word. The reused v3 lossless codec checks each
compressed value against its actual source before JSON is written; v3 table data,
fields, tags and physical layouts are not reused.

## Reproduce

Run from the sibling lean directory using the repository's pinned Rust nightly:

```sh
python3 scripts/bounded_fv.py --mib 3072 --resident-mib 4096 --seconds 300 \
  --log /tmp/airbender-v2-native-export.log -- python3 scripts/check_native_setup.py
```

This runs offline locked cargo check before the scoped single-job build, compares
regeneration byte for byte with the pinned fixture, checks equivalent binary
image/text input and rejects partial/oversized words before output. Dependencies
are isolated by this crate's manifest/lock; build output stays in lean/.lake.
The standard lean/scripts/check_all.py gate runs it under the same global lock,
sampled process-tree memory ceilings and wall budget. Do not run it alongside Lean.

The binary accepts either --fixture OUTPUT.json or IMAGE.bin TEXT.bin OUTPUT.json.
Use it only under the same bounded watchdog. Output is written to the requested
local path after all lossless and JSON roundtrip checks pass.

## Trust and scope

The [Lean certificates](../lean/Airbender/Proofs/WordMemory/NativeSetup.lean) prove
properties of imported literal data, including the complete ROM/separator/range
rows and unsupported decoder/image tails. The [public bridge](../lean/Airbender/Review/Trace/Families/WordMemory/Setup.lean)
connects this fixture's actual ROM rows to Sail byte reads after explicit padding.
General native program construction, other families, timestamp19, full physical
trace assembly/normalization/LDE, Rust/JSON/Lean emission refinement and argument
soundness remain separate. Hash identities are in the [provenance record](../lean/artifacts/provenance.json).
