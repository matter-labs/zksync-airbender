# 2^21 L1 wrap EVM verifier

The wrap verifier checks the GKR and WHIR parts of the L1 wrap proof in one
transaction. The canonical proof and operation mode come from
the `.l1` bundle of `fixtures/chains/pessimistic_conjecture/l1.json.zlib`. Packing and the WHIR
schedule come from the wrap's ProverConfig; the expected PC comes from the guest
binary and must match the bundle.

`merged/` contains the verifier with embedded setup data and Foundry tests.
`negative/wrong_final_pc/` differs only in the final PC the decoder pins.

Deploy `GkrWhirVerifier(registry)` with a registry implementing
`IVerificationRegistry`. Its constructor embeds the setup frontier, cap image and
GKR term table directly after the verifier runtime, followed by the registry ABI
word. Verification reads the setup with `codecopy`, using offsets relative to the
code tail so Solidity's metadata trailer cannot shift the data. No separate data
contract is deployed. The generated `GkrWhirVerifierCode` contract supplies runtime
code to the constructor; deploy `GkrWhirVerifier`, not that runtime template.

The verifier targets Glamsterdam's EIP-7954 size limit of 65,536 bytes; its runtime
exceeds the earlier 24,576-byte limit. Use Foundry v1.9.0 and solc 0.8.38. The
projects compile for `osaka` because solc's Amsterdam target is experimental, and
run tests with `hardfork = "amsterdam"` and `code_size_limit = 65536`. Keep the
transaction gas cap disabled: Foundry's CREATE harness does not pass the EIP-8037
state-gas reservoir to CREATE when that cap is enabled. The plain CREATE test
asserts the size dependency and reports the deployed size and CREATE gas delta.

Send the raw bytes in `single_tx_calldata.hex` to the verifier, without an ABI selector.
On success it reports `(publicInput, auxInput)` to the registry and returns the
same 64-byte tuple: final registers x10..x17 and x18..x25 (little-endian u32s).
x18..x25 hold the recursion chain hash, which
identifies the proven program and every recursion verifier above it; the
verifier does not check it. A production registry must accept only approved
verifier addresses (`msg.sender`), each pinned to one setup embedded in its runtime code,
and compare `auxInput` with the expected chain hash of the program it accepts.

From the repository root, with Foundry v1.9.0 first on PATH:

```sh
cargo test -p verifier_evm --release --test generate_contracts -- --ignored
cargo test -p verifier_evm --release --test flatten_calldata -- --ignored
sh verifier_evm/generated_contracts/run_merged.sh
```

`../deploy.sh` builds this L1 project and deploys only the registry and verifier;
`../send_proof.sh` sends the committed L1 single-transaction calldata. Both scripts
expect a Glamsterdam-capable RPC.

The EVM CI job runs these producers and rejects any changed or new output
path under verifier_evm. For proof and setup-frontier regeneration, follow the
[fixture README](../../../fixtures/README.md).
