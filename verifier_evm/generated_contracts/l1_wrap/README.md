# 2^21 L1 wrap EVM verifier

The F1 verifier checks the GKR and WHIR parts of the L1 wrap proof in one
transaction. The canonical proof and operation mode come from
the `.l1` bundle of `fixtures/chains/pessimistic_conjecture/l1.json.zlib`. Packing and the WHIR
schedule come from the wrap's ProverConfig; the expected PC comes from the guest
binary and must match the bundle.

`merged_f1/` contains the verifier, SetupFrontier and Foundry tests.
`negative/f1_wrong_final_pc/` differs only in the final PC the decoder pins.

Deploy SetupFrontier first, then deploy `GkrWhirVerifier(registry, setupFrontier)`
with that address and a registry implementing IVerificationRegistry. The
constructor checks the SetupFrontier code hash against the generated constant;
each verification checks it again before reading the data. The address is an
immutable constructor input and can differ between deployments. SetupFrontier
holds the setup nodes, cap and GKR term table as runtime code after a STOP byte.

Send the raw bytes in `single_tx_f1.hex` to the verifier, without an ABI selector.
On success it reports `(publicInput, auxInput, setupCommitment)` to the registry
and returns the same tuple: final registers x10..x17, x18..x25 (little-endian u32s),
and Keccak256 of the setup cap. x18..x25 hold the recursion chain hash, which
identifies the proven program and every recursion verifier above it; the
verifier does not check it. A production registry must restrict reporters to its
trusted verifier instances and compare `auxInput` with the expected chain hash of
the program it accepts.

From the repository root, with Foundry on PATH:

```sh
cargo test -p verifier_evm --release --test generate_contracts -- --ignored
cargo test -p verifier_evm --release --test flatten_calldata -- --ignored
verifier_evm/generated_contracts/run_merged.sh
```

The EVM CI job runs these producers and rejects any changed or new output
path under verifier_evm. For proof and setup-frontier regeneration, follow the
[fixture README](../../../fixtures/README.md).
