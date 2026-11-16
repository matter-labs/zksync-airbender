# L1 wrap encoding invariants

The bundle paths and resolved `ProverConfig` are pinned in
[tests/common/mod.rs](tests/common/mod.rs). Auxiliary data supplies the
`OperationMode::SingleChunk` boundary state and external-challenge PoW; packing
comes from the configuration.

[seed.rs](src/seed.rs) owns transcript initialization and the verified statement.
Initial-preimage words are little-endian u32s; WHIR digest words are big-endian
u32s. Proth120 field absorptions use 16-byte big-endian values, and PoW nonces use
eight big-endian bytes. A PoW step absorbs its nonce even at difficulty zero.

[replay_gkr_points](src/encoding/replay.rs) is an encoding oracle. It checks
transcript order, shape and the WHIR batching claim; it does not verify the full
proof or PoW difficulty. Proof acceptance belongs to the generated Solidity
verifier and [WHIR template](src/templates/whir.sol). The calldata decoder rejects
unconsumed input.

The statement passed to `IVerificationRegistry.markVerified` is
`publicInput || auxInput` (64 bytes). The two words concatenate registers
x10..x17 and x18..x25 as little-endian u32s;
[verified_mark](src/seed.rs) computes the same tuple. The registry must accept
only approved verifier addresses (`msg.sender`), each pinned to one setup embedded in its
runtime code, and compare `auxInput` with the expected recursion chain hash.

The setup frontier, cap image and GKR term table are embedded in the deployed
verifier code, with their existing STOP/nodes/cap/table layout unchanged. Reads
use `codecopy` at a tail-relative offset; the constructor takes only the registry
address. The verifier targets Glamsterdam's EIP-7954 size limit. Tests use Foundry
v1.9.0 with the Amsterdam hardfork; solc 0.8.38 compiles for Osaka while its
Amsterdam target is experimental.

[encoding_roundtrip.rs](tests/encoding_roundtrip.rs) checks round
factorization, including exceptional challenges. Run Rust checks with
`cargo test -p verifier_evm --tests`; cryptographic acceptance and rejection
controls require [run_merged.sh](generated_contracts/run_merged.sh).

Proof and setup-frontier producer commands are in the
[fixture README](../fixtures/README.md).
The EVM producers read `.l1` from the CLI `l1.json` artifact. The
[contract harness README](generated_contracts/l1_wrap/README.md) gives contract
and calldata producer commands. The CI producer-and-diff check validates
committed contracts against current inputs and templates.
