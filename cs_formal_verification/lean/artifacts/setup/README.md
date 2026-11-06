# Setup data

`blake-round.json`: native setup of the six-column BLAKE2 round circuit
(192 generic lookups, 6 table regions, trace length 1048576). Source of truth
for `Human.Circuits.Blake2Round.Tables.Setup`.

Provenance:

- Generator: `execution_prover/examples/export_setup_json.rs` and
  `prover/src/gkr/prover/setup_artifact.rs`, commit `9241b4aca` on `mb_fvc_antonio`
  (ported from `origin/codex/lean-circuit-verification`, unchanged logic).
- Command: `cargo run --release -p execution_prover --example export_setup_json -- blake-round - - blake-round.json`
- Source tree: `c1a662222` (`origin/av_gkr_compiler`, the PR base), run from a
  detached worktree. The generator at HEAD `cs/src` produces the legacy 208-query
  round (4 columns, 55 regions) and so cannot produce this file.
- `circuit` equals `cs/compiled_circuits/blake2_with_extended_control_layout_no_caches_gkr.json`
  at HEAD (the circuit Lean imports): checked with `==`.
- sha256 `333f3d6334e077a39cac5bc562bc98ac6b2ec95163d0cc0375e7206929259909`,
  identical to Antonio's `formal_verification/lean/artifacts/setup/blake-round.json`
  and to the manifest value.
- Cargo: no tracked `Cargo.lock` at HEAD, so `--locked` pins nothing here; the
  output depends on the cs/setups source, not dependency versions.

Row meaning (slop/Slop/Blake2Round/Setup/): `Rows.setupRow_eq` proves that every
one of the 2^20 decoded rows equals the region formula (`Spec.spec0`..`spec5`):
rows 0..606207 are the six XOR regions, rows 606208.. are all zero (tag 0).
Short blocks (<= 512 rows) are checked row by row by `decide +kernel` walks in
`Col*Walk`/`Col*Part*` (12 modules, longest ~75 s); long affine/periodic blocks
are matched by shape and proved algebraically, never expanded. The padding rows
cannot satisfy a query: `Circuit.blakeRoundQueries` (human/Human/Import/Parse.lean)
requires every query's tag column to be a constant in {4, 19, 20, 55, 56, 57}.

## Split Keccak workers

`keccak-column-parity.json`, `keccak-theta-rho.json`, `keccak-chi5.json`: native setups of the
three split Keccak-f[1600] workers (CSRs 0x7CD, 0x7CC, 0x7CE; 8/9/11 columns, trace length
4194304). Source of truth for `Human.Circuits.KeccakSplit.Tables.Setup`.

| file | sha256 |
|---|---|
| `keccak-column-parity.json` | `e3ceeb5372616a87cfacfe888a0847bad784bf94cad81e5c143a1ff77d47919d` |
| `keccak-theta-rho.json` | `66d98adf0070f516b1b5c299ed5b5a2f935819a83bfe6191a3f3ed24033b04d1` |
| `keccak-chi5.json` | `3908223fc7221242c3004e472d63950440cfbbec4ad9f88e1842d6a45fe92710` |

All three are identical to Antonio's `formal_verification/lean/artifacts/setup/` files and
manifest values (`origin/codex/lean-circuit-verification`), and each file's `circuit` equals
the imported `cs/compiled_circuits/keccak_*_layout_no_caches_gkr.json` (checked with `==`).
Command: `cargo run --release -p execution_prover --example export_setup_json -- keccak-column-parity - - keccak-column-parity.json`
(likewise `keccak-theta-rho`, `keccak-chi5`), run at this branch after the upstream merge
`049f2aa24` (sources = `c1a662222`) with the split-Keccak arms of the exporter restored
(the commit that adds this paragraph); `cargo check -p execution_prover --examples` passes.
Output byte-identical to the committed files (and to a first export from a detached
`c1a662222` tree). The same exporter at this tree also reproduces `blake-round.json`
(sha256 `333f3d63…`), so the detached-tree step above is no longer needed.
