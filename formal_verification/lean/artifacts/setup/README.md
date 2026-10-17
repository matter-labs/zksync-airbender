# Native setup artifacts

The Rust setup command exports the actual materialized columns, native table
regions, decoder rows, unused setup rows and virtual 16-/19-bit range tables.
Each document includes the circuit object used for setup and the selected
program's image/text words. Field values in setup columns are canonical residues;
the embedded circuit retains its existing Montgomery coefficient representation.

Affine, dense and periodic blocks are lossless encodings of those values. The
exporter checks every compressed physical column against the materialized column
before writing. No table-generation formula is imported in place of the data.

Generate one circuit's complete lookup setup:

```sh
cargo run --locked -p execution_prover --example export_setup_json -- \
  add-sub IMAGE.bin TEXT.bin OUTPUT.json
```

Image and text files contain little-endian u32 words; the command uses the native
program-padding and setup builders. The default is the no-cache circuit used by
FV. Other family names are `jump-branch`, `mul-div`, `shift-binop`, `word-memory`,
`subword-memory` and `unified`. The four workers (`bigint`, `blake-g`, `blake-round`,
`keccak`) and `inits-and-teardowns` take `- -` for their program-independent inputs.
Initialization/teardown gate verification is authorized after table integration.

The retained production-shape artifacts use image and text
words `[0x13, 0x00408093, 0x6f, 0x007181b3]`, with native zero padding. Ordinary
circuits use FullUnsigned; unified setup uses Reduced. The bigint setup is
program-independent, as are the hash workers and initialization setup.
`manifest.json` records native source and artifact hashes. `decoder-smoke.json` is a separate small test-shape export
that exercises fixed tables, tagged decoder rows and both range polynomials.

From the Lean directory:

```sh
lake exe airbender_import --setup artifacts/setup/add-sub.json artifacts/setup/bigint.json
```

`Import/Setup.lean` parses the typed data and validates field values, domains and
region metadata against the embedded circuit. `Import/SetupEmbed.lean` emits
literal data and Clean static tables. Source bytes are retained, and Lake tracks
the input files. Parsing and emission retain the same fidelity boundary as
circuit importing; cryptographic table authentication and lookup soundness remain
separate. The shared 13-/16-/19-bit tables now import these artifacts, with their
membership bounds proved in `Proofs/Tables/ImportedRanges.lean`. Bigint, the
G/Keccak controllers, both G/round XOR tables and all Keccak fixed tables use imported data and
kernel-checked semantics. Region slicing retains periodic interiors and checks
every decoded value against JSON; balanced literal arrays avoid deep syntax.
Standard fixed-table consumers likewise use imported rows, with mathematical
characterizations under `Proofs/Tables`. Independently imported unified fixed
regions are checked against the shared relations, including all four XOR
rotations. Native IDs and offsets drive index hints; logical enumeration may
reorder the physical regions.

Bigint's six fixed-table regions now use the exported native generic-table extent
and columns. The importer emits constant, ascending and cyclic literal arrays
compactly only after comparing every parsed value. Structural Lean proofs recover
the exact carry ranges and low-byte values across all 1,390,592 real rows,
including compression blocks that cross native region boundaries. Existing bigint
lookup and multiplication proofs consume those imported rows with their original
field scope. Native field casts are checked against the imported signed row view;
no assumed table equivalence is used. Parser regressions compare all emitted
bigint template values with the JSON data. This does not validate bigint control
words or worker participation/ROM enforcement.

BLAKE2 G's controller imports native table ID 28 with all nine physical columns.
The importer slices the parsed region into compact data, checking every selected
value against the complete columns and preserving the native region metadata.
`Proofs/Blake2G/ImportedController.lean` checks all 512 rows against the controller
reference and the concrete circuit setup, including keys, seven outputs and tag.
Existing control, address and worker consumers now use those imported outputs;
the generalized arbitrary-controller interface is preserved. Runtime regressions
compare every emitted controller value with the JSON. G/round XOR regions are
also imported and checked.

Keccak's controller imports native table ID 37 and all eight physical columns.
`Proofs/Keccak/ImportedController.lean` checks all 4,096 keys, six outputs and tag
against the reference and concrete setup, covering every inactive and invalid
fallback row. Separate 512-key certificates cover each field over the full domain.
Existing physical-slot, address and worker consumers use imported
outputs; generalized arbitrary controllers and all existing fixtures retain their
scope. Runtime regressions compare all 32,768 emitted field values, native
metadata and source bytes against the JSON.

Keccak's five fixed regions (IDs 0/4/38/39/40) import all 1,245,185 real rows and
all physical columns. `Proofs/Keccak/ImportedFixed.lean` checks XOR/Iota/Chi,
both rotation outputs, keys, padding/tags and native signed casts. Existing
lookup consumers retain their generic fields, inverses and arbitrary controllers.
The proved row equality connects the imported data to the existing mathematical
relation, so the earlier lookup soundness arguments are reused.
The importer shares only identical imported literal arrays. Interval certificates
assemble the rotation proof without expanding a million rows; the 2,046 stored
rotation template values are checked individually. Runtime regressions compare
every emitted fixed row and stored template with JSON.

The selected word-, halfword- and byte-ROM regions retain every address/control
combination and native zero-padded image word. Kernel proofs connect their keys,
outputs, padding and tags to independently imported public image bytes. Decoder
imports retain all real rows, unsupported sentinels, fixed-prefix tags and the
whole committed tail for all seven machine artifacts. Their supported rows are
checked against original Sail decoding of independently imported text. Public
byte/configuration binding is explicit; the earlier arbitrary-program claims
retain their scope. No table-content equivalence is supplied by the caller.

`airbender_tests` compares emitted source bytes, metadata and every expanded
region/decoder value with JSON, independently of the structural kernel
certificates. Affine slice validation checks equal starts and strides over the
whole overlap; all other values are compared individually. The imported-data
semantic proofs do not establish Rust refinement, cryptographic authentication,
F02/F03/F04 enforcement or AIH-336's accelerated/full-proof validation.
