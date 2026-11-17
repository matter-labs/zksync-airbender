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

Row meaning (proven/Proven/Blake2Round/Setup/): `Rows.setupRow_eq` proves, with the kernel scans of
`Proven.Setup.Native.BlakeRound`, that every one of the 2^20 decoded rows equals the region formula
(`Spec.spec0`..`spec5`):
rows 0..606207 are the six XOR regions, rows 606208.. are all zero (tag 0).
The padding rows cannot satisfy a query: `Circuit.blakeRoundQueries` (human/Human/Import/Columns.lean)
requires every query's tag column to be a constant in {4, 19, 20, 55, 56, 57}.

## How the import works

`import_setup_blocks` (human/Human/Import/SetupEmit.lean) reads each setup JSON with the proved `Json.parse` and
emits the trace length, every generic column and the two virtual range columns as the JSON blocks themselves
(`affine`, `dense`, `periodic`). The JSON reader (`parseSetup`) is the trusted step. Kernel claims give the meaning
of the rows: each states that a table definition equals the imported rows on the complete trace domain, with the
column order of the native setup. The kernel checks every column with the scans of
[generate_setup_scans.py](../../scripts/generate_setup_scans.py) (`proven/Proven/Setup/Native/`): short blocks row
by row, long blocks on one period with an algebraic proof of the period (`Proven.Setup.Scan`).

| setup | claim |
|---|---|
| `bigint` | `Bigint.SetupImportClaim` |
| `blake-g` | `Blake2G.Control.SetupImportClaim` |
| `keccak` | `Keccak.Controller.SetupImportClaim` |
| `shift-binop` | `Verification.ShiftBinopImportClaim` |
| `add-sub`, `jump-branch`, `mul-div`, `word-memory` | `Compiler.NativeFixedRows.…ImportClaim` |
| table 26 of `mul-div` | `Compiler.NativeSetups.Range13ImportClaim` |
| the six worker setups, with their range columns | `Compiler.NativeWorkerSetup.SetupImportClaim` |
| `blake-round` | `Blake2Round.SetupProofs.setupRow_eq` (proven/; the table definition reads the imported rows) |
| `keccak-column-parity`, `keccak-theta-rho`, `keccak-chi5` | `Keccak.Split.….SetupProofs.setupRow_eq` (proven/; the table definitions read the imported rows) |

The CPU claims use the setup fixture program: the four words `[0x13, 0x00408093, 0x6f, 0x007181b3]`
(`Compiler.NativeSetups.fixtureWords`) for the ROM rows, and its decoder rows. The decoder smoke fixture comes from
the `setup_json_roundtrip_preserves_materialized_columns_and_program` Rust test; no claim reads it, and the Lean
build does not import it. `inits-and-teardowns` has no generic lookup columns.

Not covered by a kernel claim:

- `subword-memory` and `unified`: the compiled comparison of
  [the fixed-row test library](../../test/Tests/NativeFixedRows/Bindings.lean) (`check_native_grid`, trusted) binds
  their fixed regions, with the fixture ROM words.

## Split Keccak workers

`keccak-column-parity.json`, `keccak-theta-rho.json`, `keccak-chi5.json`: native setups of the
three split Keccak-f[1600] workers (CSRs 0x7CD, 0x7CC, 0x7CE; 8/9/11 columns, trace length
4194304). Source of truth for `Human.Circuits.KeccakSplit.Tables.Setup`.

The [input check](../../scripts/check_compiler_captures.py) checks every setup
content pin and each hash in this table.

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
its zero key (zeros but the tag); all later rows are padding (tag 0). The kernel scans of
`proven/Proven/Setup/Native/Keccak{ColumnParity,ThetaRho,Chi5}` check every column against
its fast formula (the controller rows row by row), and `columns_eq` makes the fast formulas
equal to `Spec.spec*`.

## Public setup data

[NativePublicSetup.lean](../../human/Human/Compiler/NativePublicSetup.lean) states the public data binding for
arbitrary ROM bytes and native decoder projections. The native machine corollaries use this binding to derive CPU
constraints and public decoder membership. Capacity, nonzero masks and omitted zero coordinates are explicit public
setup properties. A fixed fixture does not prove the Rust setup generator for every program.
