# Native v2 setup table export

This standalone crate calls the pinned dev word-memory table driver, ROM/separator
constructors, decoder preprocessor/materializer and 16-bit scalar table generator.
The arithmetic mode calls AddSubLuiAuipcMopDecoder through the same native decoder
APIs. A separate scalar mode also reuses the exact pinned timestamp generation clause
and native bit-width constant, without building the prover crate.
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

The binary accepts --fixture OUTPUT.json, --scalars OUTPUT.json,
IMAGE.bin TEXT.bin OUTPUT.json, --arithmetic-fixture OUTPUT.json or
--arithmetic TEXT.bin OUTPUT.json, --decoder-padding OUTPUT.json, --control OUTPUT.json,
--control-decoder-fixture OUTPUT.json or --control-decoder TEXT.bin OUTPUT.json.
Use it only under the same bounded watchdog. Output is written to the requested
local path after all lossless and JSON roundtrip checks pass.

## Trust and scope

The [Lean certificates](../lean/Airbender/Proofs/WordMemory/NativeSetup.lean) prove
properties of imported literal data, including the complete ROM/separator/range
rows and unsupported decoder/image tails. The [public bridge](../lean/Airbender/Review/Trace/Families/WordMemory/Setup.lean)
connects this fixture's actual ROM rows to Sail byte reads after explicit padding.
General native program construction, other families, full physical
trace assembly/normalization/LDE, Rust/JSON/Lean emission refinement and argument
soundness remain separate. Hash identities are in the [provenance record](../lean/artifacts/provenance.json).

The second pinned fixture orders LW, UNIMP, SW and LW-to-x0. The same unchanged
native binary image/text API regenerates it byte for byte. Supported decoder PCs
remain 0, 8 and 12 around the unsupported slot at four. [The sparse certificate](../lean/Airbender/Proofs/WordMemory/NativeSparseSetup.lean)
constructs actual public Sail source data and proves equality of every exported
decoder row, including the interior hole and complete tail. This adds no general
Rust/Sail decoder refinement or physical setup/argument claim.

The program-independent [scalar artifact](../lean/artifacts/setup/scalars-native.json)
contains complete range16/timestamp19 prefixes in two lossless affine blocks.
Its mode calls the existing range16 API and copies the native three-line timestamp
clause verbatim with the cs-reexported constant. The standard gate checks clause
identity against pinned native source, every compressed value and exact output.
[Symbolic certificates](../lean/Airbender/Proofs/Tables/NativeScalars.lean) cover all
prefix values plus the separate source-shaped active zero-padding model, deriving
exact original Clean range meanings. The final normalization row and physical
trace/multiplicity/LDE/argument refinement remain outside this claim.

The [arithmetic fixture](../lean/artifacts/setup/arithmetic-native.json) contains
ADD, signed ADDI, SUB to x0, LUI/AUIPC with raw funct3 bits, an UNIMP hole at PC 20
and ADD at original PC 24. All 1,048,576 ten-column native rows are retained.
[Independent original Sail certificates](../lean/Airbender/Proofs/AddSub/NativeSetup.lean)
construct its actual public sparse setup and prove every exported row equal,
including holes/tail. A full native ADD witness exercises post-hole membership
and the short source claim. Fixture/binary modes reproduce identical output and
reject partial/oversized text before output. The native decoder's custom modular
MOPs are outside this concrete certificate; general Rust decoder agreement,
arbitrary-program certificates and physical trace/argument refinement remain open.

The tiny [decoder-padding artifact](../lean/artifacts/setup/decoder-padding-native.json)
calls the same native decoder-padding API used beyond the regional prefix in
physical setup assembly. It exports ten canonical minus-one values with JSON
roundtrip checks. [Symbolic active-row certificates](../lean/Airbender/Proofs/Tables/NativeDecoder.lean)
retain every extra active row, prove the sentinel is already present in each
actual prefix and derive exact membership. Source comments mentioning zeros do
not change the executable sentinel. No 2^24-row allocation is needed; reserved
normalization, general Rust trace/LDE refinement and argument enforcement remain
separate. The standard gate reproduces this artifact byte for byte.

The [native control artifact](../lean/artifacts/setup/jump-control-native.json)
is produced by --control OUTPUT.json through the actual jump/branch/SLT table
driver. It retains all four fields of every cleanup/conditional tuple: tags
17/43, offsets 0/65536 and lengths 65536/128, with no synthesized dummy row.
[Certificates](../lean/Airbender/Proofs/JumpBranchSlt/ControlTables.lean) cover the
large cleanup domain symbolically and all 128 conditional rows by finite kernel
checks. [The native circuit claim](../lean/Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean)
derives exact control/cleanup effects from both actual fixed queries. Public
program/decoder and original Sail family execution remain separate, as do
physical trace/normalization/LDE and Rust/argument refinement. The standard gate
regenerates this artifact byte for byte using the unchanged lossless codec.

The [signed control decoder fixture](../lean/artifacts/setup/jump-decoder-native.json)
uses the actual pinned signed jump/branch/SLT decoder through the same native
preprocessor/materializer. Both fixture and little-endian text modes reproduce
JAL -4 (raw funct3 7), an UNIMP hole and original SLTIU-to-x0 at PC 8, retaining
all 1,048,576 ten-column rows and the native minus-one tail. Partial/oversized text
rejects before output. Separate strict Lean profiles reject crossed arithmetic/
control or unsigned-only artifacts. [Independent Sail certificates](../lean/Airbender/Proofs/JumpBranchSlt/NativeSetup.lean)
reuse the arithmetic proof structure to establish every exported row equals
actual public construction. The short exported-decoder claim consumes full native
constraints and actual membership, deriving source evidence and PC bounds. This
concrete input certificate leaves arbitrary-program Rust decoder refinement,
initialized original control execution and physical trace/argument binding open.

The subword offset mode accepts --subword-offset LAYOUT.json OUTPUT.json and
materializes only the actual native offset/trap table. Its table ID comes from
the native table and its offset comes from the supplied compiled v2 layout.
The pinned artifact retains all 2,097,152 four-field rows at native ID 44 and
offset 65,537; the standard gate reproduces it byte for byte. Independent Lean
certificates check its complete width/limb/trap semantics, including the explicit
native misaligned-load-to-x0 exception. Remaining subword regions, full circuit
constraints, original instruction execution and physical setup/argument binding
are separate. No dependency, codec, memory ceiling or other exporter mode changes.

The subword load mode accepts --subword-load LAYOUT.json OUTPUT.json and
materializes only the actual native load-data table. Native ID 45 and its
compiled placement come from the unchanged generator and supplied v2 layout.
The pinned artifact keeps all 2,097,152 tagged rows at offset 2,162,689, including
odd-halfword and unused keys; the standard gate reproduces it byte for byte.
Lean checks exact signed/unsigned outputs from the preselected limb/offset/funct3
key and derives canonical bounds. Full circuit acceptance, original instruction
execution and physical argument binding remain separate. The shared codec,
dependencies, memory limits and other exporter modes are unchanged.
