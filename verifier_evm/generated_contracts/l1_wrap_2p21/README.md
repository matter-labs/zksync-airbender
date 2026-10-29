# 2^21 L1 wrap EVM verifier

The F1 verifier checks the GKR and WHIR parts of the CPU L1 wrap proof in one
transaction. The canonical proof and operation mode come from
`prover_pipeline/fixtures/l1_reference_2p21/l1_bundle.json`. Packing and the WHIR
schedule come from the wrap's ProverConfig; the expected PC comes from the guest
binary and must match the bundle.

`merged_f1/` contains the verifier, SetupFrontier and Foundry tests.
`negative/f1_wrong_final_pc/` differs only in the expected final PC.

Deploy SetupFrontier first, then deploy `GkrWhirVerifier(registry, setupFrontier)`
with that address and a registry implementing IVerificationRegistry. The
constructor checks the SetupFrontier code hash against the generated constant;
each verification checks it again before reading the data. The address is an
immutable constructor input and can differ between deployments. SetupFrontier
holds the setup nodes, cap and GKR term table as runtime code after a STOP byte.

Send the raw bytes in `single_tx_f1.hex` to the verifier, without an ABI selector.
On success it reports `(publicInput, auxInput, setupCommitment)` to the registry
and returns the same tuple: final registers x10..x17, x18..x25 (little-endian u32s),
and Keccak256 of the setup cap. A production registry must restrict reporters to
its trusted verifier instances.

From the repository root, with Foundry on PATH:

```sh
cargo test -p verifier_evm --release --test generate_contracts -- --ignored
cargo test -p verifier_evm --release --test flatten_calldata -- --ignored
verifier_evm/generated_contracts/run_merged.sh --no-gas
```

The EVM CI job runs these producers and rejects any changed or new output
path under verifier_evm. For proof and setup-frontier regeneration, follow
REGENERATE in prover_pipeline/src/l1_reference.rs and run its ignored
export_l1_wrap_setup_frontier test before the EVM producers.
