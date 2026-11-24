# L1 wrap EVM verifiers

The wrap verifier checks the GKR and WHIR parts of the L1 wrap proof in one
transaction. The canonical proof and operation mode come from
the `.l1` bundle of `fixtures/chains/<mode>/l1.json.zlib`, where `<mode>` is
`pessimistic_conjecture` or `ethproofs_soundcalc`. Packing and the WHIR schedule
come from the wrap's ProverConfig. The expected PC comes from the guest binary
and must match the bundle.

Each mode's `merged/` directory contains its verifier with embedded setup data
and Foundry tests. The contract producer also regenerates the ignored `negative/`
projects for each mode. `wrong_final_pc` pins a different final PC. Each PoW
control raises one difficulty above the committed proof's leading-zero count.
The producer replays the proof transcript to compute these counts, checks the
64-bit calldata nonce bound and asserts that each negative source differs from
the real verifier on one line.
The merged suite deploys all controls and requires rejection of the honest proof.
The `ood_pow_*` projects cover every OOD-PoW gate. The suite also alters
an OOD value.

Generate the verifier for one registry implementing `IVerificationRegistry`, then deploy
`GkrWhirVerifier()` with no constructor arguments. The registry address is an input to
`generate_wrap_verifier`, compiled into the runtime alongside the final PC and setup.
Regenerate the verifier whenever the registry address changes. The committed generator and
Foundry tests use `0x78D549f2A140923c517c23b008DFfE979B3c4E91`, the TestRegistry CREATE2
address for `deploy.sh`'s CreateX factory and registry salt. Tests install registry code
there with `vm.etch`. TestRegistry's source is independent of the generated verifier so its
initcode hash does not depend on the address being pinned. Generation rejects a zero address;
`deploy.sh` checks the selected address before sending transactions and checks registry code
before deploying the verifier.
After deployment it compares the complete runtime with the generated code and setup;
the verifier exposes no registry getter.

The generator derives lookup PoW from the security level and the circuit. Wrap
configs must leave the lookup PoW floor unset. The generator takes the maximum
of the lookup PoW and the wrap's external floor. Configured PoW difficulties must
fit the 64-bit calldata nonce width. The generator also requires strictly
increasing top bits.

The pessimistic wrap uses folds `[1,4,4,4,5]`, query PoW `[27,25,30,30,30]`, and folding PoW
`[10,10,9,10,10]` per step. The batching PoW derives to 14 bits. Each intermediate
oracle uses one OOD sample with PoW `[18,20,26,30]`. The final polynomial has
64 coefficients. The oracle domain logs are `[32,32,31,32,32]`, the cap is 8,
and the setup frontier is level 10. The config documents its conditional pessimistic soundness accounting. The
Ethproofs wrap has a 2^22 trace, a cap of 32 and a level-10 setup frontier.
Its ProverConfig is the source for the soundcalc certificate.

The constructor returns exactly `type(GkrWhirVerifierCode).runtimeCode || setup data`:
frontier, cap image and GKR term table, with no registry suffix. Verification reads setup with
`codecopy`, without an external data contract. Its start is `codesize() - SETUP_DATA_BYTES`;
Solidity's metadata trailer is inside the runtime prefix. Deploy `GkrWhirVerifier`, whose
constructor returns that array, rather than the `GkrWhirVerifierCode` runtime template.

The generated `<mode>/merged/MEMORY_LAYOUT.md` lists all memory regions,
SEED's disjoint absorb scratch and cache, POINT's exact bound, and setup's internal offsets.
The runtime layout is relative to the code tail: setup occupies the last `SETUP_DATA_BYTES`
bytes. `test_create_requires_glamsterdam_size_limit` reports the actual runtime size, and
`test_embedded_setup_matches_reference` checks the byte-exact runtime prefix.

`test_embedded_setup_matches_reference` checks every deployed runtime-prefix byte, the exact
setup length and its pinned Keccak256. It catches a toolchain that appends bytes after the
constructor's returned array. The Rust producer independently pins the pessimistic setup
length and hash. For Ethproofs, the producer renders the Forge expectations from the setup
in the same run, and the CI comparison of committed output catches setup changes.
`test_merged_single_tx` exercises the setup reads. `test_rejects_shifted_setup` appends a
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

With Foundry v1.9.0, solc 0.8.38 and these settings, the pessimistic verifier has a
49,391-byte runtime and 55,818-byte initcode. The CREATE test reports 79,180,101 gas.
The canonical 64,451-byte proof has a calldata floor of 4,139,864 gas.
A raw verification transaction uses 4,139,864 gas. The deployment receipt uses 76,701,896 gas.
The Anvil receipt does not expose a separate state-gas total. These figures
describe Foundry's Amsterdam model.

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

`deploy.sh <mode>` builds the selected L1 project and deploys the registry and
verifier. It reuses the default registry when its deployed runtime matches
`TestRegistry`. To deploy the second mode with the first mode's registry, set
`REGISTRY_ADDR=<first registry address>` to the address printed by the first run.
`send_proof.sh <mode> <verifier-address>` reads the committed calldata
through `<mode>/merged/script/SendProof.s.sol`
and broadcasts one verification transaction. The proof stays on disk rather than in
a command argument, whose length limit it exceeds on Linux. Both scripts expect a
Glamsterdam-capable RPC; override `RPC` and `KEY` for the node and signer in use.

The EVM CI job runs the Rust tests and these producers, builds and tests both modes,
and rejects any tracked drift or untracked output under verifier_evm. Negative renders
and Foundry outputs are ignored. For proof and setup-frontier regeneration, follow the
[fixture README](../../fixtures/README.md).
