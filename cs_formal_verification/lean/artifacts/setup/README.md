# Setup data

Format: every setup JSON here is committed in its canonical compact form, the exporter's
output: `json.dumps(v, separators=(",", ":"))` of its own value, byte for byte, without a
trailing newline. `check_circuit_json.py` (verify.sh step 1b) checks it and, on a mismatch,
prints the one-line command that canonicalizes the file. The importer parses every byte in the
interpreter, so whitespace costs build time (a re-save with indent 25 once nearly doubled
`Chi5.SetupArtifact`); never commit a re-indented copy.

`blake-round.json`: native setup of the six-column BLAKE2 round circuit
(192 generic lookups, 6 table regions, trace length 1048576). Source of truth
for `Human.Circuits.Blake2Round.Tables.Setup`.

Provenance:

- Generator: `execution_prover/examples/export_setup_json.rs` and `prover/src/gkr/prover/setup_artifact.rs`.
- Source: frozen Rust tree `9501f1f45f075b61389bb301de697514bb61bed8`.
- Command: `cargo run -p execution_prover --example export_setup_json -- blake-round - - blake-round.json`.
- The exporter output is canonicalized to compact JSON. The complete bytes must equal the imported file.
- `scripts/check_setup_freshness.py` checks every setup named in the Lake inputs against the current Rust exporter.

Row meaning (proven/Proven/Blake2Round/Setup/): `Rows.setupRow_eq` proves that every
one of the 2^20 decoded rows equals the region formula (`Spec.spec0`..`spec5`):
rows 0..606207 are the six XOR regions, rows 606208.. are all zero (tag 0).
The padding rows cannot satisfy a query: `Circuit.blakeRoundQueries` (human/Human/Import/Columns.lean)
requires every query's tag column to be a constant in {4, 19, 20, 55, 56, 57}.

## How the import structures the columns (all four files)

`import_setup_blocks` (human/Human/Import/SetupEmit.lean) cuts each column's JSON blocks at
every table edge and replaces column `c < width` of every table whose id is in
`gridCatalogue` (Xor 4, Xor7 19, Xor9 20, XorSpecialIota 38, Xor8WithCarry 55,
Xor7WithCarry 56, Xor4x3 57, KeccakXorSplit 58, KeccakXor5Nibble 64, KeccakChi5 65) by one
`grid` block: a named row formula (`GridFn`, human/Human/Import/SetupBlocks.lean). It emits a
grid block only after comparing every row of the region with the JSON value; every other
emitted block is the JSON block itself, a cut of an affine JSON block, or compared row by
row too; any mismatch fails the import. **This comparison is an elaborator responsibility,
trusted like the JSON transcription itself (`parseSetup`): it runs as elaborator code, and
the kernel never sees the JSON values of a grid region.** The proofs then work by formula:
each column is a handful of blocks; grid blocks and long affine runs are matched by shape
(`Spec`/`Shapes`) and proved equal to the row formula algebraically (`digits_eq`), the few
hundred controller rows are checked by the kernel (`Proven.Setup.Blocks.scan`).

## Split Keccak workers

`keccak-column-parity.json`, `keccak-theta-rho.json`, `keccak-chi5.json`: native setups of the
three split Keccak-f[1600] workers (CSRs 0x7CD, 0x7CC, 0x7CE; 8/9/11 columns, trace length
4194304). Source of truth for `Human.Circuits.KeccakSplit.Tables.Setup`.

| file | sha256 |
|---|---|
| `keccak-column-parity.json` | `e3ceeb5372616a87cfacfe888a0847bad784bf94cad81e5c143a1ff77d47919d` |
| `keccak-theta-rho.json` | `66d98adf0070f516b1b5c299ed5b5a2f935819a83bfe6191a3f3ed24033b04d1` |
| `keccak-chi5.json` | `3908223fc7221242c3004e472d63950440cfbbec4ad9f88e1842d6a45fe92710` |

The same exporter produces the three split files. Select `keccak-column-parity`, `keccak-theta-rho`
or `keccak-chi5`. The native freshness check compares every column, table and circuit field.

Row meaning (proven/Proven/KeccakSplit/Setup/{ColumnParity,ThetaRho,Chi5}/): `Rows.setupRow_eq`
proves that each of the 2^22 decoded rows equals the region formula (`Spec.spec*`; controller
rows via `controlAt`, `bump`, `Call.slots`, call index `Common.callIndex`), and `Members`
gives the per-tag facts used by the circuit proofs (BabyBear). Regions:
column parity: iota 38 [0, 65536), slots 62 [65536, 65658), control 63 [65658, 65780),
XOR5 64 [65780, 1114356); theta/rho: byte XOR 4 [0, 65536), XOR-and-split 58
[65536, 589824), control 59 [589824, 589945), slots 60 [589945, 590066); chi5: chi 65
[0, 1048576), control 66 [1048576, 1048697). The first row of each controller region is
its zero key (zeros but the tag); all later rows are padding (tag 0). The table regions
are grid blocks (see above; the iota constants of `XorSpecialIota` are taken from the data
and proved equal to `rcByte` in `ColumnParity.ShapesOk`); the controller regions keep their
JSON blocks and are checked row by row in `Rows`.
