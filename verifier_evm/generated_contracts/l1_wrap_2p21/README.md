# L1Wrap 2^21 EVM harness

This scaffold uses the committed 2^21 layout and `l1_wrap_2p21` prover config.
Its proof and aux inputs are
`prover/unified_circuit_proof_proth120_2p21.json` and
`prover/unified_circuit_proof_proth120_2p21_commitment_mod_aux_data.json`.
The expected final PC comes from the committed L1Feeder verifier binary and
must equal the proof aux final PC.

Until the proof is exported, normal Rust tests print explicit `SKIP` messages
for its contract and calldata drift checks. Explicit 2p21 generation fails if
either input is missing. Unselected generation visits available versions and
prints a skip for the pending proof. A present proof with missing aux fails.
If generated verifier sources or any versioned calldata output already exist,
a missing proof fails instead of skipping its drift checks.

The GKR and WHIR sources, including their zero-registry production stubs, are
generated from the real bundle. They are intentionally absent until then;
`forge build` in those empty projects does not establish verifier compilation.
The registry and tests have no verifier-source dependency, so these checks
are available now (run from the repository root):

```sh
cargo test -p verifier_evm
forge build --root verifier_evm/generated_contracts/l1_wrap_2p21/two_tx
forge test --root verifier_evm/generated_contracts/l1_wrap_2p21/two_tx \
  --match-contract RegistryBoundaryTest
```

Once the real proof and aux exist, run from the repository root:

```sh
AB_EVM_VERSION=2p21 cargo test -p verifier_evm --test generate_contracts -- --ignored
AB_EVM_VERSION=2p21 cargo test -p verifier_evm --test flatten_calldata -- --ignored
cargo test -p verifier_evm
verifier_evm/generated_contracts/run_two_tx.sh 2p21 --no-gas
forge test --root verifier_evm/generated_contracts/l1_wrap_2p21/two_tx
verifier_evm/generated_contracts/raw_tx_gas.sh 2p21 <task-owned-anvil-port>
```

`GkrWhirTwoTxTest` reads the generated sibling bytecode and versioned calldata;
missing files fail setup. Every rejection test first verifies the unmodified
2p21 pair. The serializer also writes `debug_data/l1_wrap_2p21/calldata_fields.json`
with semantic field offsets, encodings and original bytes. Mutation tests
validate those fields before flipping a byte in the opening, external PoW
nonce or final PC. The byte-flipped PC is a transcript-binding control. A
separate `test_rejects_wrong_final_pc` installs the generated
`gkr_negative/src/GkrVerifierWrongFinalPc.sol` variant, whose only difference
is its expected-PC constant (`final_pc ^ 1`), and submits the unchanged valid calldata. This
exercises the explicit PC comparison after valid transcript, PoW and sumcheck
processing. The negative variant has its own test-only Foundry project;
`run_two_tx.sh` builds it separately. The deployment script does not build or
read the negative project.

The Rust drift test checks the metadata as well as the serialized calldata.
Remove the descriptor's `allow_missing_proof` allowance when the proof bundle
is committed, making its absence a failure thereafter. All versioned deployment
and sending commands share the scripts one directory above this scaffold.
These projects use only local imports and require no remappings.

## Single-transaction proxy

`single_tx/` measures the proof as one transaction: tx calldata = GKR proof ‖
WHIR proof stream (the WHIR calldata without its committed-state preimage).
`single_tx/{gkr,gkr_negative,whir}/src/*.sol` are generated with the test pair
by the same `generate_contracts` test (`single_tx_gkr` / `single_tx_whir`): the
GKR verifier returns `[preimage][commitment][public_input][setup_commitment]`
instead of marking the registry, the WHIR verifier returns the recomputed
commitment as a fourth word. `single_tx/harness` holds the `L1VerifierSingleTx`
proxy (private immutables, no ABI surface) and its forge tests; it accepts iff
both calls succeed and the two commitments are equal. With Foundry on `PATH`,
from the repository root:

```sh
verifier_evm/generated_contracts/run_single_tx.sh 2p21 --no-gas
verifier_evm/generated_contracts/run_single_tx.sh 2p21 <task-owned-anvil-port> <out.json>
```

The gas run sends the two-tx pair and the proxy transaction as raw anvil
(Prague) transactions, checks every receipt against
`21000 + max(exec + 4·tokens, 10·tokens)`, and records execution, frames and the
computed Glamsterdam (`15000 + max(4·tokens + exec, 64·bytes)`) and Hegota
(`96·bytes`) prices with the Glamsterdam floor room.

## Format F1

F1 is the compact single-tx calldata (`verifier_evm::encoding`, module docs for
the layout): the v0 streams re-encoded with the GKR round polynomials as 2 of 4
coefficients, the WHIR sumcheck steps as 2 of 3, 123-bit packed element runs,
19-bit timestamp limb runs and `digest_bytes`-byte Merkle digests; the final PC
and the setup cap are deployment constants of the generated verifier. Every
omitted value is recomputed, so the verifiers absorb the v0 bytes unchanged.

- `debug_data/l1_wrap_2p21/single_tx_f1.hex` and `single_tx_f1_fields.json`
  (field offsets, `gkr_bytes`) are written by the `flatten_calldata` ignored test;
  `encoding_roundtrip` decodes them back to the v0 bytes.
- `single_tx/f1/{gkr,whir}` are the F1 verifiers; `single_tx/f1/gkr_negative`
  (another final PC) and `single_tx/f1/gkr_wrong_setup_cap` (another pinned
  setup cap) are test-only controls. The F1 GKR verifier decodes its calldata
  once into a memory image of the v0 GKR calldata and reads that image; the
  round functions read their `(b, c)` pairs from calldata directly.
- `single_tx/instrumented/{gkr_v0,whir_v0,gkr_f1,whir_f1}` log every keccak256
  result; `F1Oracle.t.sol` requires equal logs, GKR results, WHIR claim and
  commitment for v0 and F1 on the same proof. `F1SingleTx.t.sol` runs the F1
  proxy (acceptance with the v0 outputs, mutations of every field kind).

All of these are generated by the same `generate_contracts` ignored test and
checked by `checked_in_contracts_are_current`; `run_single_tx.sh` builds them,
runs the three forge suites and measures the F1 proxy transaction with the
v0 ones.
