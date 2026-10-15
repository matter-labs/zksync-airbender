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
