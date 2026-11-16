# 2^21 L1 wrap EVM verifier

The wrap verifier checks the GKR and WHIR parts of the L1 wrap proof in one
transaction. The canonical proof and operation mode come from
the `.l1` bundle of `fixtures/chains/pessimistic_conjecture/l1.json.zlib`. Packing and the WHIR
schedule come from the wrap's ProverConfig; the expected PC comes from the guest
binary and must match the bundle.

`merged/` contains the verifier with embedded setup data and Foundry tests.
`negative/wrong_final_pc/` differs only in the final PC the decoder pins.

Generate the verifier for one registry implementing `IVerificationRegistry`, then deploy
`GkrWhirVerifier()` with no constructor arguments. The registry address is an input to
`generate_wrap_verifier`, compiled into the runtime alongside the final PC and setup.
Regenerate the verifier whenever the registry address changes. The committed generator and
Foundry tests use `0x78D549f2A140923c517c23b008DFfE979B3c4E91`, the TestRegistry CREATE2
address for `../deploy.sh`'s CreateX factory and registry salt. Tests install registry code
there with `vm.etch`. TestRegistry's source is independent of the generated verifier so its
initcode hash does not depend on the address being pinned. Generation rejects a zero address;
`deploy.sh` checks the selected address before sending transactions and checks registry code
before deploying the verifier.

The constructor returns exactly `type(GkrWhirVerifierCode).runtimeCode || setup data`:
frontier, cap image and GKR term table, with no registry suffix. Verification reads setup with
`codecopy`, without an external data contract. Its start is `codesize() - SETUP_DATA_BYTES`;
Solidity's metadata trailer is inside the runtime prefix. Deploy `GkrWhirVerifier`, whose
constructor returns that array, rather than the `GkrWhirVerifierCode` runtime template.

The generated [memory and runtime layout](merged/MEMORY_LAYOUT.md) lists all memory regions,
SEED's disjoint absorb scratch and cache, POINT's exact bound, and setup's internal offsets.
The runtime layout is relative to the code tail: setup occupies the last `SETUP_DATA_BYTES`
bytes. `test_create_requires_glamsterdam_size_limit` reports the actual runtime size, and
`test_embedded_setup_matches_reference` checks the byte-exact runtime prefix.

`test_embedded_setup_matches_reference` checks every deployed runtime-prefix byte, the exact
setup length and its pinned Keccak256. It catches a toolchain that appends bytes after the
constructor's returned array. Changing setup length without regenerating is caught by the
Rust producer's pinned payload length/hash assertions and this deployed-code check, while
`test_merged_single_tx` exercises the resulting reads. `test_rejects_shifted_setup` appends a
byte after setup using `vm.etch`, checks rejection of the canonical proof, then restores the
code and checks acceptance. `test_rejects_altered_setup_data` covers frontier, cap and term
table mutations.

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
