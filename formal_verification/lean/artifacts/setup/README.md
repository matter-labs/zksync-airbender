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
Initialization/teardown local proof work remains deferred for discussion.

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
membership bounds proved in `Proofs/Tables/ImportedRanges.lean`. Migration of the
other table definitions and program-dependent consumers is still in progress.
