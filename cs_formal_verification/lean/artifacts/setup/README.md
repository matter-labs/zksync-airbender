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
